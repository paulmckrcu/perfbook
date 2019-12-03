/*
 * maze_seq.c: simple maze sequential solver.
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
#include "maze.h"

/* Return the distance recorded in the specified maze cell. */
cell_t maze_get_cell_distance(struct maze *mp, int row, int col)
{
	return maze_get_cell(mp, row, col) & COOKIE;
}

/* Set the distance for the specified maze cell. */
void maze_set_cell_distance(struct maze *mp, int tr, int tc, int distance)
{
	cell_t t;

	t = maze_get_cell(mp, tr, tc) & ~COOKIE;
	if (distance & ~COOKIE)
		ABORT();
	maze_set_cell(mp, tr, tc, t | distance);
}

/* Return the thread ID recorded in the specified maze cell. */
cell_t maze_get_cell_tid(struct maze *mp, int row, int col)
{
	return 1;
}

/* All cells are visited by the same thread. */
int maze_same_tids(struct maze *mp, int r1, int c1, int r2, int c2)
{
	return 1;
}

/* No additions or augmentations to the maze structure needed. */
void new_empty_maze_solve(struct maze *mp)
{
	mp->msp = NULL;
}

/*
 * Attempt to visit a cell, return non-zero if it has already been visited.
 * This odd-seeming choice allows parallel solvers to distinguish between
 * "cannot visit cell" and "some other thread beat us to that cell".
 */
int maze_try_visit_cell(struct maze *mp, int cr, int cc, int tr, int tc,
			int *nextrow, int *nextcol, int distance)
{
	if (!maze_cells_connected(mp, cr, cc, tr, tc) ||
	    maze_cell_visited(mp, tr, tc))
		return 1;
	*nextrow = tr;
	*nextcol = tc;
	maze_visit_cell(mp, tr, tc, distance);
	return 0;
}

/*
 * Attempt to solve the specified maze, return 0 if no solution exists.
 * Otherwise, return the length of the solution including the endpoints.
 */
int maze_solve(struct maze *mp, int startrow, int startcol,
	       int endrow, int endcol, unsigned long long *t)
{
	int cr = startrow;
	int cc = startcol;
	int nr;
	int nc;
	unsigned long long tstart;
	unsigned long long tstop;
	int vi = 0;

	tstart = current_time();
	maze_visit_cell(mp, cr, cc, 1);
	for (;;) {
		while (!maze_find_any_next_cell(mp, cr, cc, &nr, &nc)) {
			if (++vi >= mp->vi)
				return 0;
			cr = mp->visited[vi].row;
			cc = mp->visited[vi].col;
		}
		do {
			if (nr == endrow && nc == endcol) {
				tstop = current_time();
				*t = tstop - tstart;
				return maze_mark_solution(mp,
							  startrow, startcol,
							  endrow, endcol);
			}
			cr = nr;
			cc = nc;
		} while (maze_find_any_next_cell(mp, cr, cc, &nr, &nc));
		cr = mp->visited[vi].row;
		cc = mp->visited[vi].col;
	}
}

void maze_solve_usage(void)
{
}

int maze_solve_parse(int i, int argc, char *argv[])
{
	return i;
}
