/*
 * maze_2seq.c: maze partitioned interleaved sequential (AKA "good") solver.
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
 * Copyright (c) 2012-2019 Paul E. McKenney, IBM Corporation.
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

/* Argument structures for interleaved children. */
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
	mymcp->adj[theirtid].mr = cr;
	mymcp->adj[theirtid].mc = cc;
	mymcp->adj[theirtid].tr = tr;
	mymcp->adj[theirtid].tc = tc;
	mcsp->done = 1;
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
	t = *tp;
	if (t & VISITED) {
		record_encounter(mp, cr, cc, tr, tc);
		return 1;
	}
	*tp |= VISITED | myid;
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

struct context {
	int cr;
	int cc;
	int vi;
};

/*
 * Child maze-solver process.  Each child maintains its own ->visited[]
 * array, and the maze data structure is used to handle contention for
 * the same cell.  Such contention indicates that a pair of child threads
 * has found a path to each other.
 */
void *maze_solve_child(void *arg)
{
	struct context ctxt[2];
	int cr;
	int cc;
	int nr;
	int nc;
	int vi = 0;
	struct maze_child *mcp = (struct maze_child *)arg;
	struct maze_child_shared *mcsp = mcp->mcsp;
	struct maze *mp = mcsp->mp;
	unsigned long long tstart = current_time();

	mymcp = mcp;
	myid = mcp->myid;
	ctxt[myid].cr = mcp->visited[vi].row;
	ctxt[myid].cc = mcp->visited[vi].col;
	ctxt[myid].vi = 0;
	ctxt[!myid].cr = mcp->mcp0[!myid].visited[0].row;
	ctxt[!myid].cc = mcp->mcp0[!myid].visited[0].col;
	ctxt[!myid].vi = 0;
	cr = ctxt[myid].cr;
	cc = ctxt[myid].cc;
	do {
		/* Switch context. */
		ctxt[myid].cr = cr;
		ctxt[myid].cc = cc;
		ctxt[myid].vi = vi;
		myid = !myid;
		mymcp = &mymcp->mcp0[myid];
		mcp = mymcp;
		cr = ctxt[myid].cr;
		cc = ctxt[myid].cc;
		vi = ctxt[myid].vi;

		/*
		 * Each pass through the following loop checks one cell
		 * that has already been visited.  When a cell is found
		 * that has at least one remaining unexplored neighbor,
		 * go to the following loop to do the exploration.
		 */
		while (!maze_find_any_next_cell(mp, cr, cc, &nr, &nc)) {
			if (++vi >= mcp->vi || mcsp->done)
				goto done;
			cr = mcp->visited[vi].row;
			cc = mcp->visited[vi].col;
		}

		/*
		 * Each pass through the following loop attempts to extend
		 * the current path one cell.
		 */
		do {
			if (mcsp->done)
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
	} while (!mcsp->done);
done:

	/* Capture time, and act as passthrough for visibility information. */
	mcp->dt = current_time() - tstart;
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

/* Return true if both cells were visited by the same thread. */
int maze_same_tids(struct maze *mp, int r1, int c1, int r2, int c2)
{
	return maze_get_cell_tid(mp, r1, c1) == maze_get_cell_tid(mp, r2, c2);
}

/* Given a path through the partitions, mark the solution in the maze. */
int maze_solve_stitch_partitions(struct maze *mp,
				 int startrow, int startcol,
				 int endrow, int endcol)
{
	int d = 0;
	struct maze_child *mcp = mp->msp->mcp;
	struct rowcolpair *rcpp;

	rcpp = &mcp[0].adj[1];
	d += maze_mark_solution(mp, startrow, startcol, rcpp->mr, rcpp->mc);
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

	/* Go interleave self between the two child "threads". */
	if (!maze_solve_start_assign(mp, 0, startrow, startcol) ||
	    !maze_solve_start_assign(mp, 1, endrow, endcol))
		ABORT();
	maze_solve_child(&mcp[0]);
	mp->vi += mcp[0].vi + mcp[1].vi;
	maze_solve_map_adj(mp);

	/* Collect timing and mark solution. */
	tstop = current_time();
	*tm = tstop - tstart;
	if (mcp->mcsp->done)
		d = maze_solve_stitch_partitions(mp, startrow, startcol,
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
	fprintf(stderr, "\t--threadstats\n");
	fprintf(stderr, "\t\tEnable printing of per-thread work statistics.\n");
	fprintf(stderr, "\t\tDefault: No printing.\n");
}

int maze_solve_parse(int i_in, int argc, char *argv[])
{
	int i = i_in;
	
	while (i < argc) {
		if (strcmp(argv[i], "--threadstats") == 0) {
			threadstats = 1;
		} else
			return i;
		i++;
	}
	return i;
}
