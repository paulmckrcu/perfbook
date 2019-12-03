/*
 * maze_part.c: maze partitioned parallel (AKA "good") solver.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2011-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <time.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>
#include "maze.h"

/* Argument structures for pthread_create() children. */
struct maze_child_shared {
	struct maze *mp;
	int done;
	int endrow;
	int endcol;
};

struct rowcolpair{
	int mr;		/* My row. */
	int mc;		/* My column. */
	int tr;		/* Their row. */
	int tc;		/* Their column. */
};

struct maze_child {
	struct maze_child *mcp0;
	struct maze_child_shared *mcsp;
	int myid;
	pthread_t mytid;
	int startrow;
	int startcol;
	int vi;
	struct rowcol *visited;
	struct rowcolpair *adj;
	int see_start;
	int see_start_snap;
	int see_end;
	int see_end_snap;
	unsigned long long dt;
};

/* Private maze-structure addition for parallel solver distances. */
struct maze_solve_private {
	struct maze_child *mcp;
	struct cell distance[0];
};

struct maze_child __thread *mymcp;
int threadstats;

#include "maze_parallel.h"

/*
 * Propagate reachability to the start or the end from mcp1 to mcp2.
 * When any thread can see both the start and the end, the maze has
 * been solved, so set the "done" flag.
 *
 * This vaguely resembles a link-state routing algorithm.
 */
void maze_solve_propagate(struct maze_child *mcp1, struct maze_child *mcp2)
{
	struct maze_child_shared *mcsp = mymcp->mcsp;

	if (__sync_fetch_and_add(&mcp1->see_start, 0)) {
		(void)__sync_lock_test_and_set(&mcp2->see_start, 1);
		if (__sync_fetch_and_add(&mcp2->see_end, 0))
			WRITE_ONCE(mcsp->done, 1);
	}
	if (__sync_fetch_and_add(&mcp1->see_end, 0)) {
		(void)__sync_lock_test_and_set(&mcp2->see_end, 1);
		if (__sync_fetch_and_add(&mcp2->see_start, 0))
			WRITE_ONCE(mcsp->done, 1);
	}
}

/* Record an encounter between a pair of threads. */
void record_encounter(struct maze *mp, int cr, int cc, int tr, int tc)
{
	int theirtid;
	struct maze_child_shared *mcsp;

	if (mymcp == NULL || nthreads == 1)
		return;  /* Not yet solving the maze or only one thread. */
	mcsp = mymcp->mcsp;
	theirtid = maze_get_cell_tid(mp, tr, tc);
	if (theirtid == myid)
		return; /* We  ran into ourselves, so ignore. */
	(void)__sync_lock_test_and_set(&mymcp->adj[theirtid].mr, cr);
	mymcp->adj[theirtid].mc = cc;
	mymcp->adj[theirtid].tr = tr;
	mymcp->adj[theirtid].tc = tc;
	if (nthreads == 2)
		WRITE_ONCE(mcsp->done, 1);
	maze_solve_propagate(mymcp, &mymcp->mcp0[theirtid]);
	maze_solve_propagate(&mymcp->mcp0[theirtid], mymcp);
}

/* Attempt to visit a cell, return 0 if it has already been visited.  */
int maze_try_visit_cell(struct maze *mp, int cr, int cc, int tr, int tc,
			int *nextrow, int *nextcol, int distance)
{
	cell_t t;
	cell_t *tp;
	int vi;

	if (!maze_cells_connected(mp, cr, cc, tr, tc))
		return -1;
	tp = maze_get_cell_addr(mp, tr, tc);
	do {
		t = READ_ONCE(*tp);
		if (t & VISITED) {
			record_encounter(mp, cr, cc, tr, tc);
			return 1;
		}
	} while (!__sync_bool_compare_and_swap(tp, t, t | VISITED | myid));
	maze_set_cell_distance(mp, tr, tc, distance);
	*nextrow = tr;
	*nextcol = tc;

	/* If we are solving the maze, mymcp is non-NULL.  */
	if (mymcp != NULL) {
		/* Use this thread's state. */
		vi = mymcp->vi++;
		mymcp->visited[vi].row = tr;
		mymcp->visited[vi].col = tc;
		if (nthreads == 1 &&
		    tr == mymcp->mcsp->endrow && tc == mymcp->mcsp->endcol)
			mymcp->mcsp->done = 1;
	} else {
		/* Use global state. */
		vi = mp->vi++;
		mp->visited[vi].row = tr;
		mp->visited[vi].col = tc;
	}
	return 0;
}

/* Initialize the auxiliary data structures used by the parallel solver. */
void maze_solve_init(struct maze *mp)
{
	int i;
	int j;
	struct maze_solve_private *msp = mp->msp;
	struct maze_child *mcp;
	struct maze_child_shared *mcsp;

	mcp = (struct maze_child *)malloc(sizeof(*mcp) * nthreads);
	mcsp = (struct maze_child_shared *)malloc(sizeof(*mcsp));
	if (mcp == NULL || mcsp == NULL) {
		fprintf(stderr, "Out of memory.\n");
		ABORT();
	}
	msp->mcp = mcp;
	mcsp->mp = mp;
	mcsp->done = 0;
	for (i = 0; i < nthreads; i++) {
		mcp[i].mcp0 = mcp;
		mcp[i].mcsp = mcsp;
		mcp[i].myid = i;
		mcp[i].startrow = -1;
		mcp[i].startcol = -1;
		mcp[i].vi = 0;
		if (i == 0)
			mcp[i].visited = mp->visited;
		else
			mcp[i].visited = (struct rowcol *)
				malloc(mp->nrows * mp->ncols *
				       sizeof(struct rowcol));
		mcp[i].adj = (struct rowcolpair *)
			malloc(nthreads * sizeof(struct rowcolpair));
		if (mcp[i].visited == NULL || mcp[i].adj == NULL) {
			fprintf(stderr, "Out of memory.\n");
			ABORT();
		}
		for (j = 0; j < nthreads; j++) {
			mcp[i].adj[j].mr = -1;
			mcp[i].adj[j].mc = -1;
			mcp[i].adj[j].tr = -1;
			mcp[i].adj[j].tc = -1;
		}
		mcp[i].see_start = i == 0;
		mcp[i].see_start_snap = i == 0;
		mcp[i].see_end = i == 1;
		mcp[i].see_end_snap = i == 1;
	}
}

/*
 * Assign a child-thread starting point within the maze.  Return 1 if
 * successful, return 0 if not.  For example, if some other thread
 * already is starting at the desired point, a second attempt to assign
 * that same point will fail.  Just ABORT() if invalid starting point
 * given.
 */
int maze_solve_start_assign(struct maze *mp, int tid, int r, int c)
{
	cell_t *cp;
	int i;
	struct maze_child *mcp = mp->msp->mcp;

	/* Die if the point lies outside of the maze. */
	if (!maze_cell_exists(mp, r, c) || tid >= nthreads)
		ABORT();

	/*
	 * Return 0 if this point is already assigned to some other thread.
	 * Or if some other point is already assigned to this thread, for
	 * that matter.
	 */
	cp = maze_get_cell_addr(mp, r, c);
	if (*cp & VISITED || mcp[tid].startrow != -1)
		return 0;

	/* Assign the point. */
	mcp[tid].startrow = r;
	mcp[tid].startcol = c;
	mcp[tid].visited[0].row = r;
	mcp[tid].visited[0].col = c;
	mcp[tid].vi = 1;
	*cp |= VISITED | tid;
	maze_set_cell_distance(mp, r, c, 1);
	return 1;
}

/* Randomly assign any remaining thread's starting points. */
void maze_solve_start_random(struct maze *mp)
{
	int i;
	int r;
	int c;
	struct maze_child *mcp = mp->msp->mcp;

	for (i = 0; i < nthreads; i++)
		if (mcp[i].startrow == -1)
			do {
				r = (int)(drandom() * mp->nrows);
				c = (int)(drandom() * mp->ncols);
			} while (!maze_solve_start_assign(mp, i, r, c));
}

/*
 * Assign an anti-diagonal stripe of starting points spread evenly along
 * the diagonal running from the upper right to the lower left.
 * If they don't all fit, spread the remainder randomly.
 */
void maze_solve_start_antidiagonal(struct maze *mp)
{
	int i;
	int j;
	struct maze_child *mcp = mp->msp->mcp;
	int n = 0;

	for (i = 0; i < nthreads; i++)
		if (mcp[i].startrow == -1)
			n++;
	if (n > mp->ncols)
		n = mp->ncols;
	i = 1;
	for (j = 0; j < nthreads; j++) {
		if (mcp[j].startrow != -1)
			continue;
		maze_solve_start_assign(mp, j,
					mp->nrows -
					maze_row_col_frac(mp->nrows, i, n + 1),
					maze_row_col_frac(mp->ncols, i, n + 1));
		i++;
	}
	maze_solve_start_random(mp);
/*&&&&*/for (i = 0; i < nthreads; i++) fprintf(stderr, "Start(%d): (%d, %d)\n", i, mcp[i].startrow, mcp[i].startcol);
}

/*
 * Assign a horizontal stripe of starting points evenly spread across
 * the width of the maze.  If they don't all fit, spread the remainder
 * randomly.
 */
void maze_solve_start_diagonal(struct maze *mp)
{
	int i;
	int j;
	struct maze_child *mcp = mp->msp->mcp;
	int n = 0;

	for (i = 0; i < nthreads; i++)
		if (mcp[i].startrow == -1)
			n++;
	if (n > mp->ncols)
		n = mp->ncols;
	i = 1;
	for (j = 0; j < nthreads; j++) {
		if (mcp[j].startrow != -1)
			continue;
		maze_solve_start_assign(mp, j,
					maze_row_col_frac(mp->nrows, i, n + 1),
					maze_row_col_frac(mp->ncols, i, n + 1));
		i++;
	}
	maze_solve_start_random(mp);
}

/*
 * Assign a horizontal stripe of starting points evenly spread across
 * the width of the maze.  If they don't all fit, spread the remainder
 * randomly.
 */
void maze_solve_start_horizontal(struct maze *mp)
{
	int i;
	int j;
	struct maze_child *mcp = mp->msp->mcp;
	int n = 0;
	int row = maze_row_col_frac(mp->nrows, 1, 2);

	for (i = 0; i < nthreads; i++)
		if (mcp[i].startrow == -1)
			n++;
	if (n > mp->ncols)
		n = mp->ncols;
	i = 1;
	for (j = 0; j < nthreads; j++) {
		if (mcp[j].startrow != -1)
			continue;
		maze_solve_start_assign(mp, j, row,
					maze_row_col_frac(mp->ncols, i, n + 1));
		i++;
	}
	maze_solve_start_random(mp);
}

/*
 * Assign a vertical stripe of starting points evenly spread across
 * the height of the maze.  If they don't all fit, spread the remainder
 * randomly.
 */
void maze_solve_start_vertical(struct maze *mp)
{
	int col = maze_row_col_frac(mp->ncols, 1, 2);
	int i;
	int j;
	struct maze_child *mcp = mp->msp->mcp;
	int n = 0;

	for (i = 0; i < nthreads; i++)
		if (mcp[i].startrow == -1)
			n++;
	if (n > mp->nrows)
		n = mp->nrows;
	i = 1;
	for (j = 0; j < nthreads; j++) {
		if (mcp[j].startrow != -1)
			continue;
		maze_solve_start_assign(mp, j,
					maze_row_col_frac(mp->nrows, i, n + 1),
					col);
		i++;
	}
	maze_solve_start_random(mp);
}

/*
 * Data for maze_solve_start_spread().  This data is used to spread the
 * the child-thread starting points across the maze.  The first three
 * arrays have relative positions, where:
 *
 *	0 = Left or top edge of the maze.
 *	1 = One-quarter of the way from the left or top edge of the maze.
 *	2 = Half-way across the maze.
 *	3 = Three-quarters of the way from the left or top edge of the maze.
 *	5 = Right or bottom edge of the maze.
 *
 * The final pos[] array tells which of the first three arrays to use
 * given the index of the final thread.
 */
struct rowcol pos12359[] = {
	{ 0, 0 }, /* 1 */
	{ 4, 4 }, /* 2 */
	{ 2, 2 }, /* 3 */
	{ 4, 0 },
	{ 0, 4 }, /* 5 */
	{ 2, 1 },
	{ 3, 2 },
	{ 2, 3 },
	{ 1, 2 }, /* 9 */
};
struct rowcol pos48[] = {
	{ 0, 0 },
	{ 4, 4 },
	{ 0, 4 },
	{ 4, 0 }, /* 4 */
	{ 2, 1 },
	{ 3, 2 },
	{ 2, 3 },
	{ 1, 2 }, /* 8 */
};
struct rowcol pos67[] = {
	{ 0, 0 },
	{ 4, 4 },
	{ 2, 1 },
	{ 3, 2 },
	{ 2, 3 },
	{ 1, 2 }, /* 6 */
	{ 2, 2 }, /* 7 */
};
struct rowcol *pos[] = {
	pos12359, /* 1 thread.  */
	pos12359, /* 2 threads. */
	pos12359, /* 3 threads. */
	pos48,	  /* 4 threads. */
	pos12359, /* 5 threads. */
	pos67,	  /* 6 threads. */
	pos67,	  /* 7 threads. */
	pos48,	  /* 8 threads. */
	pos12359, /* 9 threads. */
};

/*
 * Spread the per-thread starting points in a sensible pattern across the
 * maze.  If there are more than nine threads, spread the remainder
 * randomly.
 */
void maze_solve_start_spread(struct maze *mp)
{
	int i;
	int n = nthreads;
	int r;
	int c;
	struct rowcol *rc;
	int rowspread[5];
	int colspread[5];

	for (i = 0; i < 5; i++) {
		rowspread[i] = maze_row_col_frac(mp->nrows, i, 4);
		colspread[i] = maze_row_col_frac(mp->ncols, i, 4);
	}
	if (n > 9)
		n = 9;
	rc = pos[n - 1];
	for (i = 0; i < n; i++) {
		r = rowspread[rc[i].row];
		c = colspread[rc[i].col];
		(void)maze_solve_start_assign(mp, i, r, c);
	}
	maze_solve_start_random(mp);
}

/* Default thread-starting-point assignment function. */
void (*threadstartfunc)(struct maze *mp) = maze_solve_start_random;

/*
 * Assign each thread's starting point.  The first thread always starts at
 * the maze start, and the second thread (if there is one) always starts
 * at the maze end.  Any other threads are assigned as specified.
 */
void maze_solve_start(struct maze *mp, int startrow, int startcol,
		      int endrow, int endcol)
{
	if (!maze_solve_start_assign(mp, 0, startrow, startcol))
		ABORT();
	if (nthreads > 1 && !maze_solve_start_assign(mp, 1, endrow, endcol))
		ABORT();
	threadstartfunc(mp);
}

/*
 * Check start/end visibility.  If we have recently gained more visibility,
 * propagate it to all of the thread that we have encountered or that
 * have encountered us.
 */
int maze_solve_child_done_check(void)
{
	int i;
	struct maze_child_shared *mcsp = mymcp->mcsp;
	int myid = mymcp->myid;
	int need_propagate = 0;
	struct maze_child *theirmcp;

	if (nthreads <= 2)
		return READ_ONCE(mcsp->done);
	if (!mymcp->see_start_snap &&
	    __sync_fetch_and_add(&mymcp->see_start, 0)) {
		mymcp->see_start_snap = 1;
		need_propagate = 1;
	}
	if (!mymcp->see_end_snap &&
	    __sync_fetch_and_add(&mymcp->see_end, 0)) {
		mymcp->see_end_snap = 1;
		need_propagate = 1;
	}
	if (!need_propagate)
		return READ_ONCE(mcsp->done);
	for (i = 0; i < nthreads; i++) {
		if (i == mymcp->myid)
			continue;
		theirmcp = &mymcp->mcp0[i];
		if (__sync_fetch_and_add(&mymcp->adj[i].mr, 0) != -1 ||
		    __sync_fetch_and_add(&theirmcp->adj[myid].mr, 0) != -1)
			maze_solve_propagate(mymcp, theirmcp);
	}
	return READ_ONCE(mcsp->done);
}

/*
 * Child maze-solver process.  Each child maintains its own ->visited[]
 * array, and the maze data structure is used to handle contention for
 * the same cell.  Such contention indicates that a pair of child threads
 * has found a path to each other.
 */
void *maze_solve_child(void *arg)
{
	int cr;
	int cc;
	int nr;
	int nc;
	cpu_set_t mask;
	int vi = 0;
	struct maze_child *mcp = (struct maze_child *)arg;
	struct maze_child_shared *mcsp = mcp->mcsp;
	struct maze *mp = mcsp->mp;
	static const struct timespec ts = { .tv_sec = 0, .tv_nsec = 3000 };
	unsigned long long tstart = current_time();

	mymcp = mcp;
	myid = mcp->myid;
	CPU_ZERO(&mask);
	CPU_SET(myid, &mask);
	sched_setaffinity(0, sizeof(mask), &mask);
	cr = mcp->visited[vi].row;
	cc = mcp->visited[vi].col;
	do {
		/*
		 * Each pass through the following loop checks one cell
		 * that has already been visited.  When a cell is found
		 * that has at least one remaining unexplored neighbor,
		 * go to the following loop to do the exploration.
		 */
		while (!maze_find_any_next_cell(mp, cr, cc, &nr, &nc)) {
			if (++vi >= mcp->vi || READ_ONCE(mcsp->done))
				goto done;
			cr = mcp->visited[vi].row;
			cc = mcp->visited[vi].col;
		}

		/*
		 * Each pass through the following loop attempts to extend
		 * the current path one cell.
		 */
		do {
			if (READ_ONCE(mcsp->done))
				goto done;
			cr = nr;
			cc = nc;
		} while (maze_find_any_next_cell(mp, cr, cc, &nr, &nc));

		/*
		 * Reset back to the start of this path in case there is
		 * another unexplored cell adjacent to it.
		 */
		cr = mcp->visited[vi].row;
		cc = mcp->visited[vi].col;
	} while (!maze_solve_child_done_check());
done:

	/* Capture time, and act as passthrough for visibility information. */
	mcp->dt = current_time() - tstart;
	if (nthreads > 2)
		while (!maze_solve_child_done_check())
			nanosleep(&ts, NULL); /* In case hardware bus-locks. */
	return NULL;
}

/*
 * The thread encounters are stored, but only by the thread that discovered
 * the encounter.  Copy any encounters to the location that the other
 * thread would have recorded them.
 */
void maze_solve_map_adj(struct maze *mp)
{
	int i;
	int j;
	struct maze_child *mcp = mp->msp->mcp;

	for (i = 0; i < nthreads; i++)
		for (j = 0; j < nthreads; j++)
			if (mcp[i].adj[j].mr == -1) {
				mcp[i].adj[j].mr = mcp[j].adj[i].tr;
				mcp[i].adj[j].mc = mcp[j].adj[i].tc;
				mcp[i].adj[j].tr = mcp[j].adj[i].mr;
				mcp[i].adj[j].tc = mcp[j].adj[i].mc;
			}
}

/* Route through the partitions, given the encounter data. */
int maze_solve_route_partitions(struct maze *mp, int *path)
{
	int i;
	struct maze_child *mcp = mp->msp->mcp;
	int pathidx = 1;

	if (nthreads == 1)
		return 1;
	path[0] = 0;
	path[1] = 1;
	if (nthreads == 2)
		return 1;
	for (;;) {
		for (; path[pathidx] < nthreads; path[pathidx]++) {
			for (i = 0; i < pathidx; i++)
				if (path[i] == path[pathidx])
					break;  /* Already been here. */
			if (i >= pathidx &&
			    mcp[path[pathidx - 1]].adj[path[pathidx]].mr != -1)
				break;  /* Found a possible next partition. */
		}
		if (path[pathidx] == 1)
			return 1;  /* Found partition containing destination. */
		if (pathidx < nthreads - 1 && path[pathidx] < nthreads)
			path[++pathidx] = 1;  /* Look for next partition. */
		else {
			if (pathidx == 1)
				return 0;  /* No solution. */
			path[--pathidx]++;  /* Backtrack. */
		}
	}
}

/* Advance the solution marking by one cell. */
void maze_mark_advance_cell(struct maze *mp, int cr, int cc, int *nr, int *nc)
{
	cell_t *cp = maze_get_cell_addr(mp, cr, cc);

	*cp |= SOLUTION;
	if (maze_get_cell_distance(mp, cr, cc) == 1)
		ABORT();
	if (!maze_is_prev_cell(mp, cr, cc, cr - 1, cc, nr, nc) &&
	    !maze_is_prev_cell(mp, cr, cc, cr + 1, cc, nr, nc) &&
	    !maze_is_prev_cell(mp, cr, cc, cr, cc - 1, nr, nc) &&
	    !maze_is_prev_cell(mp, cr, cc, cr, cc + 1, nr, nc))
		ABORT();
}

/* Return true if both cells were visited by the same thread. */
int maze_same_tids(struct maze *mp, int r1, int c1, int r2, int c2)
{
	return maze_get_cell_tid(mp, r1, c1) == maze_get_cell_tid(mp, r2, c2);
}

/*
 * Mark the subsolution located by a interior thread, in other words, a
 * thread other than the ones that started at the beginning and end cells.
 */
int maze_mark_subsolution(struct maze *mp, int r1, int c1, int r2, int c2)
{
	int cr1 = r1;
	int cc1 = c1;
	int cr2 = r2;
	int cc2 = c2;
	cell_t *cp;
	int d1 = maze_get_cell_distance(mp, cr1, cc1);
	int d2 = maze_get_cell_distance(mp, cr2, cc2);
	int nr;
	int nc;
	int s = 0;

	for (;;) {
		if (maze_get_cell_tid(mp, cr1, cc1) !=
		    maze_get_cell_tid(mp, cr2, cc2))
		    	ABORT();
		if (cr1 == cr2 && cc1 == cc2) {
			cp = maze_get_cell_addr(mp, cr1, cc1);
			*cp |= SOLUTION;
			return s + 1;
		}
		if (d1 > d2) {
			maze_mark_advance_cell(mp, cr1, cc1, &nr, &nc);
			s++;
			cr1 = nr;
			cc1 = nc;
			d1 = maze_get_cell_distance(mp, cr1, cc1);
		} else if (d1 <= d2 && d2 != 1) {
			maze_mark_advance_cell(mp, cr2, cc2, &nr, &nc);
			s++;
			cr2 = nr;
			cc2 = nc;
			d2 = maze_get_cell_distance(mp, cr2, cc2);
		} else
			ABORT();
	}
}

/* Given a path through the partitions, mark the solution in the maze. */
int maze_solve_stitch_partitions(struct maze *mp, int *path,
				 int startrow, int startcol,
				 int endrow, int endcol)
{
	int cr;
	int cc;
	int d = 0;
	int i;
	struct maze_child *mcp = mp->msp->mcp;
	struct rowcolpair *rcpp;

	if (nthreads == 1)
		return maze_mark_solution(mp, startrow, startcol,
					  endrow, endcol);
	rcpp = &mcp[path[0]].adj[path[1]];
	d += maze_mark_solution(mp, startrow, startcol, rcpp->mr, rcpp->mc);
	for (i = 1; path[i] != 1; i++) {
		cr = rcpp->tr;
		cc = rcpp->tc;
		rcpp = &mcp[path[i]].adj[path[i + 1]];
		d += maze_mark_subsolution(mp, cr, cc, rcpp->mr, rcpp->mc);
	}
	if (nthreads > 1)
		d += maze_mark_solution(mp, endrow, endcol, rcpp->tr, rcpp->tc);
	return d;
}

/*
 * Attempt to solve the specified maze, return 0 if no solution exists.
 * Otherwise, return the length of the solution including the endpoints.
 */
int maze_solve(struct maze *mp, int startrow, int startcol,
	       int endrow, int endcol, unsigned long long *tm)
{
	int d = 0;
	int i;
	struct maze_child *mcp;
	int *path;
	int solution = 0;
	void *trash;
	unsigned long long tstart;
	unsigned long long tstop;

	tstart = current_time();

	/* Allocate and initialize the shared data structures. */
	if (nthreads >= mp->nrows * mp->ncols)
		usage("", "--nthreads = %d > rows*cols = %d\n",
		      nthreads, mp->nrows * mp->ncols);
	maze_solve_init(mp);
	mcp = mp->msp->mcp;
	mcp->mcsp->endrow = endrow;
	mcp->mcsp->endcol = endcol;

	/* Spawn the children. */
	maze_solve_start(mp, startrow, startcol, endrow, endcol);
	for (i = 1; i < nthreads; i++)
		if (pthread_create(&mcp[i].mytid, NULL,
				   maze_solve_child, &mcp[i]) != 0)
			ABORT();

	/* The parent is the first child.  Never grow up!!! */
	maze_solve_child(&mcp[0]);
	mp->vi += mcp[0].vi;

	/* Clean up the kids.  You cannot completely fail to grow up... */
	for (i = 1; i < nthreads; i++) {
		pthread_join(mcp[i].mytid, &trash);
		mp->vi += mcp[i].vi;
	}

	/* Stitch the per-thread solutions together. */
	path = (int *)malloc(sizeof(*path) * nthreads);
	if (path == NULL) {
		fprintf(stderr, "Out of memory.\n");
		ABORT();
	}
	maze_solve_map_adj(mp);
	if (maze_solve_route_partitions(mp, path))
		solution = 1;

	/* Collect timing and mark solution. */
	tstop = current_time();
	*tm = tstop - tstart;
	if (solution)
		d = maze_solve_stitch_partitions(mp, path, startrow, startcol,
						 endrow, endcol);
	if (threadstats) {
		double avg = mp->vi / (double)nthreads;

		/* Visit-based skew statistics. */
		fprintf(stderr, "Visit skew:");
		for (i = 0; i < nthreads; i++)
			fprintf(stderr, " %d: %d (%g)",
				i, mcp[i].vi, mcp[i].vi / avg);
		fprintf(stderr, "\n");

		/* Time-based skew statistics. */
		avg = (double)*tm;
		fprintf(stderr, "Time skew:");
		for (i = 0; i < nthreads; i++)
			fprintf(stderr, " %d: %g ms (%g)",
				i, mcp[i].dt / 1000000., mcp[i].dt / avg);
		fprintf(stderr, "\n");
	}
	return d;
}

void maze_solve_usage(void)
{
	fprintf(stderr, "\t--nthreads nthreads\n");
	fprintf(stderr, "\t\tNumber of threads to use in solution.\n");
	fprintf(stderr, "\t\tDefault: 2.\n");
	fprintf(stderr, "\t--threadstart method\n");
	fprintf(stderr, "\t\tThread start-location method to use.\n");
	fprintf(stderr, "\t\tantidiagonal: Spread diagonally from upper right "
			    "to lower left.\n");
	fprintf(stderr, "\t\tdiagonal: Spread diagonally from upper left "
			    "to lower right.\n");
	fprintf(stderr, "\t\thorizontal: Spread horizontally.\n");
	fprintf(stderr, "\t\tvertical: Spread vertically.\n");
	fprintf(stderr, "\t\tspread: Spread in 2D patterns.\n");
	fprintf(stderr, "\t\trandom: Spread randomly.\n");
	fprintf(stderr, "\t\tExcess threads are spread randomly.\n");
	fprintf(stderr, "\t\tDefault: random.\n");
	fprintf(stderr, "\t--threadstats\n");
	fprintf(stderr, "\t\tEnable printing of per-thread work statistics.\n");
	fprintf(stderr, "\t\tDefault: No printing.\n");
}

int maze_solve_parse(int i_in, int argc, char *argv[])
{
	int i = i_in;
	
	while (i < argc) {
		if (strcmp(argv[i], "--nthreads") == 0) {
			if (i >= argc - 1)
				usage(argv[0],
				      "--nthreads requires #threads\n");
			nthreads = strtol(argv[++i], NULL, 0);
			if (nthreads <= 0)
				usage(argv[0],
				      "--nthreads must be non-negative\n");
		} else if (strcmp(argv[i], "--threadstart") == 0) {
			if (i >= argc - 1)
				usage(argv[0],
				      "--threadstart requires method\n");
			i++;
			if (strcmp(argv[i], "antidiagonal") == 0)
				threadstartfunc = maze_solve_start_antidiagonal;
			else if (strcmp(argv[i], "horizontal") == 0)
				threadstartfunc = maze_solve_start_diagonal;
			else if (strcmp(argv[i], "horizontal") == 0)
				threadstartfunc = maze_solve_start_horizontal;
			else if (strcmp(argv[i], "vertical") == 0)
				threadstartfunc = maze_solve_start_vertical;
			else if (strcmp(argv[i], "spread") == 0)
				threadstartfunc = maze_solve_start_spread;
			else if (strcmp(argv[i], "random") == 0)
				threadstartfunc = maze_solve_start_random;
			else
				usage(argv[0],
				      "--threadstart invalid method %s\n",
				      argv[i]);
		} else if (strcmp(argv[i], "--threadstats") == 0) {
			threadstats = 1;
		} else
			return i;
		i++;
	}
	return i;
}
