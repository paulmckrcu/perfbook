/*
 * maze_parallel.c: definitions common to parallel solvers
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

int __thread myid;
int nthreads = 2;

/* Get the address of the specified cell in the private addition. */
static cell_t *maze_solve_get_cell_addr(struct maze *mp, int tr, int tc)
{
	if (!maze_cell_exists(mp, tr, tc))
		ABORT();
	return &mp->msp->distance[tr * mp->ncols + tc].c;
}

/* Return the distance recorded for the specified maze cell. */
cell_t maze_get_cell_distance(struct maze *mp, int row, int col)
{
	return *maze_solve_get_cell_addr(mp, row, col);
}

/* Set the distance for the specified maze cell. */
void maze_set_cell_distance(struct maze *mp, int tr, int tc, int distance)
{
	*maze_solve_get_cell_addr(mp, tr, tc) = distance;
}

/* Return the thread ID recorded in the specified maze cell. */
cell_t maze_get_cell_tid(struct maze *mp, int row, int col)
{
	return maze_get_cell(mp, row, col) & COOKIE;
}

/* Allocate the ->msp structure. */
void new_empty_maze_solve(struct maze *mp)
{
	mp->msp = (struct maze_solve_private *)malloc(sizeof(*mp->msp) +
						      mp->nrows * mp->ncols *
						      sizeof(struct cell));
	if (mp->msp == NULL) {
		fprintf(stderr, "Out of memory\n");
		ABORT();
	}
}
