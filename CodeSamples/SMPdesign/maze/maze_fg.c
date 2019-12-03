/*
 * maze_fg.c: simple maze fine-grained parallel (AKA "bad") solver.
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

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <time.h>
#include <string.h>
#include <pthread.h>
#include "maze.h"

/* Argument structures for pthread_create() children. */
struct maze_child_shared {
	struct maze *mp;
	int vi;
	int done;
	int endrow;
	int endcol;
};

struct maze_child {
	struct maze_child_shared *mcsp;
	int myid;
	pthread_t mytid;
	int vi;
};

/* Private maze-structure addition for parallel solver distances. */
struct maze_solve_private {
	struct cell distance[0];
};

int threadstats;

#include "maze_parallel.h"

/*
 * Cells visited by different threads have no special status in this
 * parallel solver, so just say that any given pair of cells was visited
 * by the same thread.  In contrast, partitioning parallel solvers need
 * to differentiate regions located by different threads in order to
 * successfully stitch together the full solution.
 */
int maze_same_tids(struct maze *mp, int r1, int c1, int r2, int c2)
{
	return 1;
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
		if (t & VISITED)
			return 1;
	} while (!__sync_bool_compare_and_swap(tp, t, t | VISITED | myid));
	maze_set_cell_distance(mp, tr, tc, distance);
	*nextrow = tr;
	*nextcol = tc;
	vi = __sync_add_and_fetch(&mp->vi, 1);
	mp->visited[vi].row = tr;
	__sync_synchronize();
	WRITE_ONCE(mp->visited[vi].col, tc);
	return 0;
}

/*
 * Child maze-solver process.  Contends with other children for elements
 * of the ->visited[] array, which acts like a work queue.
 */
void *maze_solve_child(void *arg)
{
	int cr = -1;
	int cc = -1;
	int nr;
	int nc;
	int vi = -1;
	struct maze_child *mcp = (struct maze_child *)arg;
	struct maze_child_shared *mcsp = mcp->mcsp;
	struct maze *mp = mcsp->mp;

	myid = mcp->myid;
	for (;;) {
		/*
		 * Each pass through the following loop checks one cell
		 * that has already been visited.  When a cell is found
		 * that has at least one remaining unexplored neighbor,
		 * go to the following loop to do the exploration.
		 */
		while (cr == -1 ||
		       !maze_find_any_next_cell(mp, cr, cc, &nr, &nc)) {
			vi = __sync_add_and_fetch(&mcsp->vi, 1);

			/*
			 * If all the threads are waiting for another
			 * cell to be added to the visited list, we
			 * are done and the maze has no solution.
			 */
			if (vi >= READ_ONCE(mp->vi) + nthreads) {
				WRITE_ONCE(mcsp->done, -1);
				return NULL;
			}

			/*
			 * Otherwise, wait for the cell to be visited or
			 * for one of the other threads to find the
			 * end cell.
			 */
			while ((vi > READ_ONCE(mp->vi) ||
			        READ_ONCE(mp->visited[vi].col) < 0) &&
			       !READ_ONCE(mcsp->done))
			       	continue;
			if (READ_ONCE(mcsp->done))
				return NULL;

			/* check of .col before read of .row. */
			__sync_synchronize();
			cr = mp->visited[vi].row;
			cc = mp->visited[vi].col;
		}

		/*
		 * Each pass through the following loop attempts to extend
		 * the current path one cell.
		 */
		do {
			/* Did we find the solution? */
			if (nr == mcsp->endrow && nc == mcsp->endcol) {
				WRITE_ONCE(mcsp->done, 1);
				return NULL;
			}

			/* If not, advance to the next cell and try again. */
			cr = nr;
			cc = nc;
		} while (maze_find_any_next_cell(mp, cr, cc, &nr, &nc));

		/*
		 * Reset back to the start of this path in case there is
		 * another unexplored cell adjacent to it.  Note that
		 * we already know that .col is >= 0.
		 */
		cr = mp->visited[vi].row;
		cc = mp->visited[vi].col;
	}
}

/*
 * Attempt to solve the specified maze, return 0 if no solution exists.
 * Otherwise, return the length of the solution including the endpoints.
 */
int maze_solve(struct maze *mp, int startrow, int startcol,
	       int endrow, int endcol, unsigned long long *tm)
{
	int d;
	int i;
	int j;
	struct maze_child *mcp;
	struct maze_child_shared mcs;
	cell_t t;
	void *trash;
	unsigned long long tstart;
	unsigned long long tstop;

	tstart = current_time();

	/* Allocate and initialize the shared data structures. */
	mcp = (struct maze_child *)malloc(nthreads * sizeof(*mcp));
	if (mcp == NULL) {
		fprintf(stderr, "Out of memory\n");
		ABORT();
	}
	for (i = 0; i < mp->nrows * mp->ncols; i++) {
		mp->visited[i].row = -1;
		mp->visited[i].col = -1;
		mp->msp->distance[i].c = 0;
	}

	/* Visit the first cell manually to get things started. */
	t = maze_get_cell(mp, startrow, startcol);
	maze_set_cell(mp, startrow, startcol, t | VISITED | 1);
	mp->visited[0].row = startrow;
	mp->visited[0].col = startcol;
	mp->vi = 0;
	maze_set_cell_distance(mp, startrow, startcol, 1);

	/* Initialize the shared state. */
	mcs.mp = mp;
	mcs.vi = -1;
	mcs.done = 0;
	mcs.endrow = endrow;
	mcs.endcol = endcol;

	/* Initialize the per-child state and spawn the children. */
	for (i = 0; i < nthreads; i++) {
		mcp[i].mcsp = &mcs;
		mcp[i].vi = 0;
		mcp[i].myid = i;
		if (i != 0)
			if (pthread_create(&mcp[i].mytid, NULL,
					   maze_solve_child, &mcp[i]) != 0)
				ABORT();
	}

	/* The parent is the first child.  Never grow up!!! */
	maze_solve_child(&mcp[0]);

	/* Clean up the kids.  You cannot completely fail to grow up... */
	for (i = 1; i < nthreads; i++)
		pthread_join(mcp[i].mytid, &trash);

	/* Collect timing and mark solution. */
	tstop = current_time();
	*tm = tstop - tstart;
	if (mcs.done == 1)
		d = maze_mark_solution(mp, startrow, startcol, endrow, endcol);
	if (threadstats) {
		double avg = mp->vi / (double)nthreads;
		int tid;

		/* Visit-based skew statistics. */
		for (i = 0; i < mp->nrows; i++)
			for (j = 0; j < mp->ncols; j++) {
				if (maze_get_cell(mp, i, j) & VISITED) {
					tid = maze_get_cell_tid(mp, i, j);
					mcp[tid].vi++;
				}
			}
		fprintf(stderr, "Visit skew:");
		for (i = 0; i < nthreads; i++)
			fprintf(stderr, " %d: %d (%g)",
				i, mcp[i].vi, mcp[i].vi / avg);
		fprintf(stderr, "\n");
	}

	/* Free up and return.  We leak mp->msp because main() needs it. */
	free(mcp);
	return mcs.done == 1 ? d : 0;
}

void maze_solve_usage(void)
{
	fprintf(stderr, "\t--nthreads nthreads\n");
	fprintf(stderr, "\t\tNumber of threads to use in solution.\n");
	fprintf(stderr, "\t\tDefault: 2.\n");
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
		} else if (strcmp(argv[i], "--threadstats") == 0) {
			threadstats = 1;
		} else
			return i;
		i++;
	}
	return i;
}
