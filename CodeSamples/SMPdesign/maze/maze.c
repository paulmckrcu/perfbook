/*
 * maze.c: simple maze create/solve program.
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

int line_thickness = 1;


/* Get current time in free-running nanoseconds. */
unsigned long long current_time(void)
{
	struct timespec t;

	if (clock_gettime(MAZE_CLOCK, &t) != 0)
		ABORT();
	return (unsigned long long)t.tv_sec * 1000000000ULL +
	       (unsigned long long)t.tv_nsec;
}

/* Compute the specified fraction, normally of rows or columns. */
int maze_row_col_frac(int rc, int num, int den)
{
	if (rc <= 0 || num < 0 || den <= 0)
		ABORT();
	return ((rc - 1) * num + den - 1) / den;
}

/* Set up the segment weights for the specified structure. */
void maze_set_seg_weights(struct segment_weights *swp,
			  int len, double straightfrac, double segbends)
{
	double sb = segbends;
	double sf = straightfrac;
	double tl;

	if (len <= 0)
		ABORT();
	if (sf <= 0.0)
		sf = 1.0 / (len <= 0 ? 1.0 : (double)len);
	if (sb < 0.0)
		sb = 0.0;
	tl = len * sf * (sb + 1.0);
	swp->randweight = tl / (tl + 1.0);
	swp->contweight = (tl - sb) / (tl + 1.0);
	if (swp->contweight < 0.0)
		swp->contweight = 0.0;
	if (swp->contweight > swp->randweight)
		swp->contweight = swp->randweight;
}

/* Allocate an empty maze and set up border and randomness. */
struct maze *new_empty_maze(int nrows, int ncols,
			    double straightfrac, double segbends,
			    double revisit)
{
	int i;
	int j;
	struct maze *mp;

	mp = (struct maze *)malloc(sizeof(*mp) +
				   nrows * ncols * sizeof(struct cell));
	if (mp == NULL) {
		fprintf(stderr, "Out of memory");
		ABORT();
	}
	mp->nrows = nrows;
	mp->ncols = ncols;

	/* Set up path-selection random weights. */
	maze_set_seg_weights(&mp->weights[0], ncols, straightfrac, segbends);
	maze_set_seg_weights(&mp->weights[1], nrows, straightfrac, segbends);

	/* Allocate array that tracks visited cells. */
	mp->visited = (struct rowcol *)malloc(nrows * ncols *
					      sizeof(*mp->visited));
	if (mp->visited == NULL) {
		fprintf(stderr, "Out of memory");
		ABORT();
	}
	mp->vi = 0;
	mp->lastvi = -1;
	mp->revisit = revisit;

	/* Set up border and interior. */
	maze_set_cell(mp, 0, 0, WALL_UP | WALL_LEFT);
	maze_set_cell(mp, nrows - 1, 0, WALL_DOWN | WALL_LEFT);
	maze_set_cell(mp, 0, ncols - 1, WALL_UP | WALL_RIGHT);
	maze_set_cell(mp, nrows - 1, ncols - 1, WALL_DOWN | WALL_RIGHT);
	for (i = 1; i < nrows - 1; i++) {
		maze_set_cell(mp, i, 0, WALL_LEFT);
		maze_set_cell(mp, i, ncols - 1, WALL_RIGHT);
		for (j = 1; j < ncols - 1; j++)
			maze_set_cell(mp, i, j, 0);
	}
	for (i = 1; i < ncols - 1; i++) {
		maze_set_cell(mp, 0, i, WALL_UP);
		maze_set_cell(mp, nrows - 1, i, WALL_DOWN);
	}
	new_empty_maze_solve(mp);
	return mp;
}

/* Dump out fig header. */
void maze_to_fig_header(FILE *fp)
{
	fprintf(fp, "#FIG 3.2  Produced by maze.c\n");
	fprintf(fp, "Landscape\nCenter\nInches\nLetter\n");
	fprintf(fp, "100.00\nSingle\n-2\n1200 2\n");
}

/* Output a line in fig coordinates. */
static void maze_to_fig_line(FILE *fp,
			     int x1, int y1, int x2, int y2, int pc, int depth)
{
	static char *cw = "2 1 0 %d %d -1 %d -1 0.000 0 0 -1 0 0 2\n";

	fprintf(fp, cw, line_thickness, pc, depth);
	fprintf(fp, "\t%d %d %d %d\n", x1, y1, x2, y2);
}

/* Output a solution indicator if the specified cell is part of the solution. */
void maze_to_fig_solution(FILE *fp, struct maze *mp, int row, int col, int upc)
{
	if ((maze_get_cell(mp, row, col) & SOLUTION) == 0)
		return;
	if (maze_cells_connected(mp, row, col, row - 1, col) &&
	    (maze_get_cell(mp, row - 1, col) & SOLUTION))
		maze_to_fig_line(fp, col * upc + upc / 2, row * upc,
				 col * upc + upc / 2, row * upc + upc / 2,
				 14, 51);
	if (maze_cells_connected(mp, row, col, row + 1, col) &&
	    (maze_get_cell(mp, row + 1, col) & SOLUTION))
		maze_to_fig_line(fp, col * upc + upc / 2, row * upc + upc / 2,
				 col * upc + upc / 2, row * upc + upc,
				 14, 51);
	if (maze_cells_connected(mp, row, col, row, col - 1) &&
	    (maze_get_cell(mp, row, col - 1) & SOLUTION))
		maze_to_fig_line(fp, col * upc, row * upc + upc / 2,
				 col * upc + upc / 2, row * upc + upc / 2,
				 14, 51);
	if (maze_cells_connected(mp, row, col, row, col + 1) &&
	    (maze_get_cell(mp, row, col + 1) & SOLUTION))
		maze_to_fig_line(fp, col * upc + upc / 2, row * upc + upc / 2,
				 col * upc + upc, row * upc + upc / 2,
				 14, 51);
}

/* Print a check if the cell was visited. */
void maze_to_fig_visited(FILE *fp, struct maze *mp, int row, int col, int upc)
{
	if (maze_get_cell(mp, row, col) & VISITED)
		maze_to_fig_line(fp, col * upc, row * upc,
				 (col + 1) * upc, (row + 1) * upc, 14,
				 100 + maze_get_cell_tid(mp, row, col));
}

/* Draw the wall connecting the corners of the specified cells. */
void maze_to_fig_cell_wall(FILE *fp,
			   int row1, int col1, int row2, int col2, int upc)
{
	maze_to_fig_line(fp, col1 * upc, row1 * upc, col2 * upc, row2 * upc,
			 0, 50);
			 
}

/* Draw the maze in fig format. */
void maze_to_fig(FILE * fp, struct maze *mp, int upc, int visited)
{
	int i;
	int j;

	maze_to_fig_header(fp);
	maze_to_fig_cell_wall(fp, 0, 0, 0, mp->ncols, upc);
	maze_to_fig_cell_wall(fp, 0, 0, mp->nrows, 0, upc);
	for (i = 0; i < mp->nrows; i++)
		for (j = 0; j < mp->ncols; j++) {
			if (maze_get_cell(mp, i, j) & WALL_DOWN)
				maze_to_fig_cell_wall(fp, i + 1, j,
						      i + 1, j + 1, upc);
			if (maze_get_cell(mp, i, j) & WALL_RIGHT)
				maze_to_fig_cell_wall(fp, i, j + 1,
						      i + 1, j + 1, upc);
			maze_to_fig_solution(fp, mp, i, j, upc);
			if (visited)
				maze_to_fig_visited(fp, mp, i, j, upc);
		}
}

/* Return a uniformly distributed double x such that 0 <= x < 1. */
double drandom(void)
{
	unsigned int x;

	x = random();
	return ((double)x) / ((double)RAND_MAX + 1.0);
}

/* Return a randomly selected int that is either +1 or -1. */
int pmrandom(void)
{
	unsigned int x;

	x = random();
	return ((x & 0x8000) == 0) * 2 - 1;
}

/*
 * Has the specified cell been visited?  If it does not exist, that
 * counts as having been visited.
 */
int maze_cell_visited(struct maze *mp, int row, int col)
{
	if (!maze_cell_exists(mp, row, col))
		return 1;
	return !!(maze_get_cell(mp, row, col) & VISITED);
}

/* Visit the specified cell.  Die if already visited. */
void maze_visit_cell(struct maze *mp, int row, int col, int distance)
{
	cell_t *cp = maze_get_cell_addr(mp, row, col);

	if (*cp & VISITED)
		ABORT();
	if (mp->visited != NULL) {
		if (mp->vi >= mp->nrows * mp->ncols)
			ABORT();
		mp->visited[mp->vi].row = row;
		mp->visited[mp->vi].col = col;
		mp->vi++;
	}
	*cp |= VISITED;
	maze_set_cell_distance(mp, row, col, distance);
}

/*
 * Pick a next cell, no particular preference as to direction, so go
 * along a row if possible to take advantage of cache affinity by
 * default.  -DCOLFIRST if you want otherwise.
 *
 * Return 0 if there is no adjacent unvisited cell.
 */
int maze_find_any_next_cell(struct maze *mp, int cr, int cc, int *nr, int *nc)
{
	int d = maze_get_cell_distance(mp, cr, cc) + 1;

#ifndef COLFIRST
	if (!maze_try_visit_cell(mp, cr, cc, cr, cc - 1, nr, nc, d))
		return 1;
	if (!maze_try_visit_cell(mp, cr, cc, cr, cc + 1, nr, nc, d))
		return 1;
#endif /* #ifndef COLFIRST */
	if (!maze_try_visit_cell(mp, cr, cc, cr - 1, cc, nr, nc, d))
		return 1;
	if (!maze_try_visit_cell(mp, cr, cc, cr + 1, cc, nr, nc, d))
		return 1;
#ifdef COLFIRST
	if (!maze_try_visit_cell(mp, cr, cc, cr, cc - 1, nr, nc, d))
		return 1;
	if (!maze_try_visit_cell(mp, cr, cc, cr, cc + 1, nr, nc, d))
		return 1;
#endif /* #ifdef COLFIRST */
	return 0;
}

/* Build a wall if appropriate. */
void maze_build_one_cell_wall(struct maze *mp, int wallrow, int wallcol,
			      int prevrow, int prevcol, int currow, int curcol,
			      int nextrow, int nextcol)
{
	cell_t wallbit;
	cell_t *cp;

	/* If the candidate cell is either prev or next, no wall. */
	if (wallrow == prevrow && wallcol == prevcol)
		return;
	if (wallrow == nextrow && wallcol == nextcol)
		return;

	/* If the wall cell actually exists, we need a wall. */
	if (maze_cell_exists(mp, wallrow, wallcol)) {
		/* Wall in other cell. */
		wallbit = maze_find_wallbit(wallrow, wallcol, currow, curcol);
		cp = maze_get_cell_addr(mp, wallrow, wallcol);
		*cp |= wallbit;
		/* Wall in current cell. */
		wallbit = maze_find_wallbit(currow, curcol, wallrow, wallcol);
		cp = maze_get_cell_addr(mp, currow, curcol);
		*cp |= wallbit;
	}
}

/* Build the cell walls implied by the succession of three cells. */
void maze_build_cell_walls(struct maze *mp, int prevrow, int prevcol,
			   int currow, int curcol, int nextrow, int nextcol)
{
	maze_build_one_cell_wall(mp, currow - 1, curcol, prevrow, prevcol,
				 currow, curcol, nextrow, nextcol);
	maze_build_one_cell_wall(mp, currow + 1, curcol, prevrow, prevcol,
				 currow, curcol, nextrow, nextcol);
	maze_build_one_cell_wall(mp, currow, curcol - 1, prevrow, prevcol,
				 currow, curcol, nextrow, nextcol);
	maze_build_one_cell_wall(mp, currow, curcol + 1, prevrow, prevcol,
				 currow, curcol, nextrow, nextcol);
}

/*
 * Wall in the specified cell.  This allows easy construction of
 * unsolvable mazes.  Returns 1 on success, and 0 if the specified
 * cell was not in the maze.
 */
int maze_wall_in(struct maze *mp, int row, int col)
{
	if (!maze_cell_exists(mp, row, col))
		return 0;
	if (maze_cells_connected(mp, row, col, row - 1, col))
		maze_build_one_cell_wall(mp, row - 1, col,
					 row, col, row, col, row, col);
	if (maze_cells_connected(mp, row, col, row + 1, col))
		maze_build_one_cell_wall(mp, row + 1, col,
					 row, col, row, col, row, col);
	if (maze_cells_connected(mp, row, col, row, col - 1))
		maze_build_one_cell_wall(mp, row, col - 1,
					 row, col, row, col, row, col);
	if (maze_cells_connected(mp, row, col, row, col + 1))
		maze_build_one_cell_wall(mp, row, col + 1,
					 row, col, row, col, row, col);
	return 1;
}

/* Randomly choose a next cell to build the current maze segment. */
int maze_choose_next_cell(struct maze *mp, int prevrow, int prevcol,
			  int currow, int curcol, int *nextrow, int *nextcol)
{
	int d;  /* Distance. */
	int dr; /* Delta rows. */
	int dc; /* Delta columns. */
	int nr; /* Next row. */
	int nc; /* Next column. */
	struct segment_weights *swp = &mp->weights[prevrow != currow];
	double w = drandom();

	d = maze_get_cell_distance(mp, currow, curcol);
	if (w > swp->randweight) {
		/* Time to stop. */
		return MAZE_END_SEGMENT;
	}
	if (w > swp->contweight && (prevrow != currow || prevcol != curcol)) {
		/* Erect a perpendicular vector. */
		dr = -(curcol - prevcol);
		dc = currow - prevrow;
		/* Flip the vector if randomly required. */
		if (pmrandom()) {
			dr = -dr;
			dc = -dc;
		}
		/* Try out the corresponding cell. */
		nr = currow + dr;
		nc = curcol + dc;
		if (!maze_try_visit_cell(mp, currow, curcol, nr, nc,
					nextrow, nextcol, d + 1))
			return MAZE_CONTINUE_SEGMENT;
		/* No go, try turning the opposite direction. */
		nr = currow - dr;
		nc = curcol - dc;
		if (!maze_try_visit_cell(mp, currow, curcol, nr, nc,
					nextrow, nextcol, d + 1))
			return MAZE_CONTINUE_SEGMENT;
		/* Neither worked, drop through and try straight. */
	}
	nr = currow + (currow - prevrow);
	nc = curcol + (curcol - prevcol);
	if (!maze_try_visit_cell(mp, currow, curcol, nr, nc,
				nextrow, nextcol, d + 1))
		return MAZE_CONTINUE_SEGMENT;
	/* No go, check all possibilities.  Done being picky! */
	if (maze_find_any_next_cell(mp, currow, curcol, nextrow, nextcol))
		return MAZE_CONTINUE_SEGMENT;
	/* Nowhere left to go. */
	return MAZE_STUCK_SEGMENT;
}

/* Construct one segment (or passage) in the maze. */
void maze_construct_segment(struct maze *mp, int row1, int col1,
			    int row2, int col2)
{
	int prevrow = row1;
	int prevcol = col1;
	int currow = row2;
	int curcol = col2;
	int nextrow;
	int nextcol;

	/* If starting, pick an initial direction. */
	if (prevrow == currow && prevcol == curcol) {
		if (!maze_find_any_next_cell(mp, currow, curcol,
					     &nextrow, &nextcol))
			return;
		maze_build_cell_walls(mp, prevrow, prevcol, currow, curcol,
				      nextrow, nextcol);
		prevrow = currow;
		prevcol = curcol;
		currow = nextrow;
		curcol = nextcol;
	}

	/* Each pass through the following loop advances one cell. */
	for (;;) {
		switch (maze_choose_next_cell(mp, prevrow, prevcol,
					      currow, curcol,
					      &nextrow, &nextcol)) {
		case MAZE_CONTINUE_SEGMENT:
			maze_build_cell_walls(mp, prevrow, prevcol,
					      currow, curcol, nextrow, nextcol);
			prevrow = currow;
			prevcol = curcol;
			currow = nextrow;
			curcol = nextcol;
			break;
		case MAZE_END_SEGMENT:
			maze_build_cell_walls(mp, prevrow, prevcol,
					      currow, curcol, prevrow, prevcol);
		case MAZE_STUCK_SEGMENT:
			return;
		}
	}
}

/* Remove a wall to allow another maze segment to be constructed. */
void maze_remove_wall(struct maze *mp, int currow, int curcol,
		      int otherrow, int othercol)
{
	cell_t *cp;

	cp = maze_get_cell_addr(mp, currow, curcol);
	*cp &= ~maze_find_wallbit(currow, curcol, otherrow, othercol);
	cp = maze_get_cell_addr(mp, otherrow, othercol);
	*cp &= ~maze_find_wallbit(otherrow, othercol, currow, curcol);
}

/*
 * Find a boundary between the created and inchoate portions of the maze.
 * Return 0 if the maze is now fully created.
 */
int maze_find_boundary(struct maze *mp, int *prevrow, int *prevcol,
		       int *currow, int *curcol)
{
	int d;
	int cr;
	int cc;
	int pr;
	int pc;
	int vi;
	int vi_lim;
	int vi_start;

	if (mp->lastvi == -1 || drandom() > mp->revisit)
		vi = drandom() * mp->vi;
	else
		vi = mp->lastvi;
	vi_lim = mp->vi;
	vi_start = vi;
	do {
		pr = mp->visited[vi].row;
		pc = mp->visited[vi].col;
		cr = -1;
		if (!maze_cell_visited(mp, pr - 1, pc)) {
			cr = pr - 1;
			cc = pc;
		}
		if (!maze_cell_visited(mp, pr + 1, pc) &&
		    (cr == -1 || drandom() < 0.5)) {
			cr = pr + 1;
			cc = pc;
		}
		if (!maze_cell_visited(mp, pr, pc - 1) &&
		    (cr == -1 || drandom() < 0.5)) {
			cr = pr;
			cc = pc - 1;
		}
		if (!maze_cell_visited(mp, pr, pc + 1) &&
		    (cr == -1 || drandom() < 0.5)) {
			cr = pr;
			cc = pc + 1;
		}
		if (cr != -1) {
			d = maze_get_cell_distance(mp, pr, pc);
			maze_remove_wall(mp, pr, pc, cr, cc);
			maze_visit_cell(mp, cr, cc, d + 1);
			*prevrow = pr;
			*prevcol = pc;
			*currow = cr;
			*curcol = cc;
			mp->lastvi = vi;
			return 1;
		}
		vi++;
		if (vi >= mp->vi)
			vi = 0;
		if (vi_lim != mp->vi)
			ABORT();
	} while (vi != vi_start);
	return 0; /* Maze is now finished. */
}

/* Remove visitation, solution, and distance tags to allow maze to be solved. */
void maze_unvisit_all(struct maze *mp)
{
	cell_t *cp;
	int i;
	int j;

	for (i = 0; i < mp->nrows; i++)
		for (j = 0; j < mp->ncols; j++) {
			cp = maze_get_cell_addr(mp, i, j);
			*cp &= ~(VISITED | SOLUTION | COOKIE);
			maze_set_cell_distance(mp, i, j, 0);
		}
	mp->vi = 0;
}

/* Create a full maze by repeatedly invoking maze_construct_segment(). */
struct maze *maze_create(int nrows, int ncols, int startrow, int startcol,
			 double straightfrac, double segbends, double revisit)
{
	int row1 = startrow;
	int col1 = startcol;
	int row2 = startrow;
	int col2 = startcol;
	struct maze *mp = new_empty_maze(nrows, ncols,
					 straightfrac, segbends, revisit);

	maze_visit_cell(mp, row1, col1, 1);
	maze_construct_segment(mp, row1, col1, row2, col2);
	while (maze_find_boundary(mp, &row1, &col1, &row2, &col2))
		maze_construct_segment(mp, row1, col1, row2, col2);
	if (mp->vi != mp->nrows * mp->ncols) {
		fprintf(stderr, "Leftover: mp->vi = %d vs. %d\n",
			mp->vi, mp->nrows * mp->ncols);
		ABORT();
	}
	maze_unvisit_all(mp);
	return mp;
}

/*
 * Is the second cell the predecessor to the first one along the
 * solution path?  The "backwards" order of arguments is due to
 * the fact that we traverse the solution backwards when marking it.
 */
int maze_is_prev_cell(struct maze *mp, int row1, int col1, int row2, int col2,
		      int *nextrow, int *nextcol)
{
	if (!maze_cells_connected(mp, row1, col1, row2, col2) ||
	    !maze_same_tids(mp, row1, col1, row2, col2) ||
	    maze_get_cell_distance(mp, row1, col1) -
	    maze_get_cell_distance(mp, row2, col2) != 1)
		return 0;
	*nextrow = row2;
	*nextcol = col2;
	return 1;
}

/*
 * Mark the maze's solution, working from the end to the beginning.
 * Returns the length of the solution, including the two endpoints.
 * A length of zero implies an unsolvable maze.
 */
int maze_mark_solution(struct maze *mp, int startrow, int startcol,
			int endrow, int endcol)
{
	int cr;
	int cc;
	cell_t *cp;
	int nr = endrow;
	int nc = endcol;

	for (;;) {
		cr = nr;
		cc = nc;
		cp = maze_get_cell_addr(mp, cr, cc);
		*cp |= SOLUTION;
		if (cr == startrow && cc == startcol)
			return maze_get_cell_distance(mp, endrow, endcol);
		if (!maze_is_prev_cell(mp, cr, cc, cr - 1, cc, &nr, &nc) &&
		    !maze_is_prev_cell(mp, cr, cc, cr + 1, cc, &nr, &nc) &&
		    !maze_is_prev_cell(mp, cr, cc, cr, cc - 1, &nr, &nc) &&
		    !maze_is_prev_cell(mp, cr, cc, cr, cc + 1, &nr, &nc))
			ABORT();
	}
}

/*
 * Output a maze in binary form.  This allows different solvers to be
 * compared on an equal footing, particularly when testing cache
 * alignment.  Differences in mazes can wash out large effects, so the
 * ability to compare algorithms running on exactly the same maze
 * can be quite important.
 */
int maze_binary_out(char *path, struct maze *mp)
{
	FILE *fp = fopen(path, "w");
	int i;
	int j;

	if (fp == NULL) {
		perror("maze_binary_out:");
		fprintf(stderr, "Unable to open %s\n", path);
		return 0;
	}
	fwrite(bin_file_header, strlen(bin_file_header) + 1, 1, fp);
	fwrite(mp, sizeof(*mp), 1, fp);
	for (i = 0; i < mp->nrows; i++)
		for (j = 0; j < mp->ncols; j++)
			fwrite(maze_get_cell_addr(mp, i, j), sizeof(cell_t),
			       1, fp);
	return 1;
}

/* Input a maze in binary form. */
struct maze *maze_binary_in(char *path)
{
	char buf[8];
	FILE *fp = fopen(path, "r");
	int i;
	int j;
	struct maze maze_raw;
	struct maze *mp;
	int t;

	if (fp == NULL) {
		perror("maze_binary_in:");
		fprintf(stderr, "Unable to open %s\n", path);
		return NULL;
	}
	t = fread(buf, sizeof(buf), 1, fp);
	if (strncmp(buf, bin_file_header, sizeof(buf)) != 0) {
		fprintf(stderr, "Bad header in maze_binary_in()\n");
		return NULL;
	}
	t = fread(&maze_raw, sizeof(maze_raw), 1, fp);
	mp = (struct maze *)malloc(sizeof(*mp) +
				   maze_raw.nrows * maze_raw.ncols *
				   sizeof(struct cell));
	if (mp == NULL) {
		fprintf(stderr, "Out of memory\n");
		ABORT();
	}
	*mp = maze_raw;
	mp->visited = (struct rowcol *)malloc(mp->nrows * mp->ncols *
					      sizeof(*mp->visited));
	if (mp->visited == NULL) {
		fprintf(stderr, "Out of memory");
		ABORT();
	}
	mp->vi = 0;
	mp->lastvi = -1;
	for (i = 0; i < mp->nrows; i++)
		for (j = 0; j < mp->ncols; j++)
			t = fread(maze_get_cell_addr(mp, i, j),
				  sizeof(cell_t), 1, fp);
	new_empty_maze_solve(mp);
	return mp;
}

void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "%s: Available options:\n", progname);
	fprintf(stderr, "\t--help\n");
	fprintf(stderr, "\t\tThis information.\n");
	fprintf(stderr, "I/O Options:\n");
	fprintf(stderr, "\t--input path\n");
	fprintf(stderr, "\t\tInput binary maze previously --output.\n");
	fprintf(stderr, "\t\tDefaults to no input.\n");
	fprintf(stderr, "\t--output path\n");
	fprintf(stderr, "\t\tOutput maze in binary, with solution if any.\n");
	fprintf(stderr, "\t\tDefaults to no output.\n");
	fprintf(stderr, "\t--fig path\n");
	fprintf(stderr, "\t\tOutput xfig with cell walls on layer 50\n");
	fprintf(stderr, "\t\tand solution (if any) on layer 51.\n");
	fprintf(stderr, "\t\tUse 'fig2dev -L png -m 2 -D +50' to exclude "
			    "solution.\n");
	fprintf(stderr, "\t\tDefaults to stdout.\n");
	fprintf(stderr, "\t--figupc number\n");
	fprintf(stderr, "\t\tInteger number of fig units per cell.\n");
	fprintf(stderr, "\t\tDefaults are appropriate for US Letter paper.\n");
	fprintf(stderr, "\t--figlinethickness number\n");
	fprintf(stderr, "\t\tInteger line width in fig units\n");
	fprintf(stderr, "\t\tDefaults to 1.\n");
	fprintf(stderr, "\t--figvisit\n");
	fprintf(stderr, "\t\tIndicate solution path on layer 100+.\n");
	fprintf(stderr, "\t\tDefault to no solution-visitation indication.\n");
	fprintf(stderr, "\t\t(Intended for debugging purposes.)\n");
	fprintf(stderr, "\t--nofig\n");
	fprintf(stderr, "\t\tDo not output xfig info.\n");
	fprintf(stderr, "Maze-generation options:\n");
	fprintf(stderr, "\t--generate [ rows [ cols ] ]\n");
	fprintf(stderr, "\t\tRandomly generate maze of specified size.\n");
	fprintf(stderr, "\t\tDefaults:  rows=41, cols=32.\n");
	fprintf(stderr, "\t--gen_sf straightfrac\n");
	fprintf(stderr, "\t\tExpected corridor length as fraction of side.\n");
	fprintf(stderr, "\t\tDefaults to 0.2, may be greater than 1.0.\n");
	fprintf(stderr, "\t--gen_sb segbends\n");
	fprintf(stderr, "\t\tExpected number of corridors in each segment.\n");
	fprintf(stderr, "\t\tDefaults to 4.0, may be greater than 1.0.\n");
	fprintf(stderr, "\t--gen_rv revisit\n");
	fprintf(stderr, "\t\tProbability of new segment starting at the\n");
	fprintf(stderr, "\t\tsame place as the last one.\n");
	fprintf(stderr, "\t\tDefaults to 0.2, must be 0.0 <= rv <= 1.0.\n");
	fprintf(stderr, "\t--seed seed\n");
	fprintf(stderr, "\t\tRandom-number generator seed.\n");
	fprintf(stderr, "\t\tDefaults to current time in nanoseconds.\n");
	fprintf(stderr, "\t--wall-in row col\n");
	fprintf(stderr, "\t\tWall in the specified cell.  Negative numbers\n");
	fprintf(stderr, "\t\tindicate fraction of maze: '-2 -2' is center.\n");
	fprintf(stderr, "\t\tThis may be used to build unsolvable mazes.\n");
	fprintf(stderr, "\t\tOnly one cell may be walled in per run.\n");
	fprintf(stderr, "\t\tDefault:  No walling in.\n");
	fprintf(stderr, "\tAlso uses --start from maze-solution section.\n");
	fprintf(stderr, "Maze-solution options:\n");
	fprintf(stderr, "\t--solve\n");
	fprintf(stderr, "\t\tAttempt to solve the current maze.\n");
	fprintf(stderr, "\t\tDefault:  Attempt solution.\n");
	fprintf(stderr, "\t--start row col\n");
	fprintf(stderr, "\t\tStarting point for solution.  Negative numbers\n");
	fprintf(stderr, "\t\tindicate fraction of maze: '-2 -2' is center.\n");
	fprintf(stderr, "\t\tDefault:  Upper left corner.\n");
	fprintf(stderr, "\t--end row col\n");
	fprintf(stderr, "\t\tEnding point for solution.  Negative numbers\n");
	fprintf(stderr, "\t\tindicate fraction of maze: '-2 -2' is center.\n");
	fprintf(stderr, "\t\tDefault:  Lower right corner.\n");
	fprintf(stderr, "\t--nosolve\n");
	fprintf(stderr, "\t\tDo not solve the current maze.\n");
	fprintf(stderr, "\t\tDefault:  Attempt solution.\n");
	fprintf(stderr, "\t--clear\n");
	fprintf(stderr, "\t\tClear solution from previously solved maze.\n");
	fprintf(stderr, "\t\tDefault:  Do not clear solution.\n");
	maze_solve_usage();
	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	exit(EXIT_FAILURE);
}

int main(int argc, char *argv[])
{
	unsigned long long dt;
	int i = 1;
	struct maze *mp;
	double q;
	int solved = 1;
	char *binin = NULL;
	char *binout = NULL;
	FILE *figfp = stdout;
	char *figout = NULL;
	int figupc = 300;
	int figupcgiven = 0;
	int figvisit = 0;
	int generate = 0;
	int rows = 41;
	int cols = 32;
	double straightfrac = 0.2;
	double segbends = 4;
	double revisit = 0.2;
	unsigned long seed = current_time();
	int startrow = 0;
	int startcol = 0;
	int endrow = -1;
	int endcol = -1;
	int wallin = 0;
	int wallinrow;
	int wallincol;
	int solve = 1;
	int clear = 0;

	/* Parse arguments. */
	while (i < argc) {
		if (strcmp(argv[i], "--input") == 0) {
			if (generate)
				usage(argv[0],
				      "Conflict: --input and --generate\n");
			if (i >= argc - 1)
				usage(argv[0], "--input requires path name\n");
			binin = argv[++i];
		} else if (strcmp(argv[i], "--output") == 0) {
			if (i >= argc - 1)
				usage(argv[0], "--output requires path name\n");
			binout = argv[++i];
		} else if (strcmp(argv[i], "--fig") == 0) {
			if (i >= argc - 1)
				usage(argv[0], "--fig requires path name\n");
			figout = argv[++i];
			figfp = fopen(figout, "w");
			if (figfp == NULL)
				usage(argv[0], "--fig file unwriteable\n");
		} else if (strcmp(argv[i], "--figupc") == 0) {
			if (i >= argc - 1)
				usage(argv[0],
				      "--figupc requires fig units per cell\n");
			figupc = strtol(argv[++i], NULL, 0);
			if (figupc <= 0)
				usage(argv[0],
				      "--figupc must be non-negative\n");
			figupcgiven = 1;
		} else if (strcmp(argv[i], "--figlinethickness") == 0) {
			if (i >= argc - 1)
				usage(argv[0],
				      "--figlinethickness requires number\n");
			line_thickness = strtol(argv[++i], NULL, 0);
			if (line_thickness <= 0)
				usage(argv[0],
				      "--figlinethickness must be "
				      "non-negative\n");
		} else if (strcmp(argv[i], "--figvisit") == 0) {
			figvisit = 1;
		} else if (strcmp(argv[i], "--nofig") == 0) {
			if (figfp != stdout)
				usage(argv[0], "Conflict: --fig and --nofig\n");
			figfp = NULL;
		} else if (strcmp(argv[i], "--generate") == 0) {
			generate = 1;
			if (binin)
				usage(argv[0],
				      "Conflict: --generate and --input\n");
			if (i < argc - 1 && argv[i + 1][0] != '-') {
				rows = strtol(argv[++i], NULL, 0);
				cols = rows;
			}
			if (i < argc - 1 && argv[i + 1][0] != '-')
				cols = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--gen_sf") == 0) {
			if (i >= argc - 1)
				usage(argv[0],
				      "--gen_sf requires straightfrac\n");
			straightfrac = strtod(argv[++i], NULL);
			if (straightfrac <= 0.0)
				usage(argv[0],
				      "--gen_sf requires straightfrac > 0");
		} else if (strcmp(argv[i], "--gen_sb") == 0) {
			if (i >= argc - 1)
				usage(argv[0], "--gen_sb requires segbends\n");
			segbends = strtod(argv[++i], NULL);
			if (segbends < 0.0)
				usage(argv[0],
				      "--gen_sb requires segbends >= 0\n");
		} else if (strcmp(argv[i], "--gen_rv") == 0) {
			if (i >= argc - 1)
				usage(argv[0], "--gen_rv requires revisit\n");
			revisit = strtod(argv[++i], NULL);
			if (revisit < 0.0 || revisit > 1.0)
				usage(argv[0], "--gen_rv: 0 <= revisit <= 1\n");
		} else if (strcmp(argv[i], "--seed") == 0) {
			if (i >= argc - 1)
				usage(argv[0], "--seed requires integer\n");
			seed = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--solve") == 0) {
			solve = 1;
		} else if (strcmp(argv[i], "--start") == 0) {
			if (i >= argc - 2)
				usage(argv[0], "--start requires position\n");
			startrow = strtol(argv[++i], NULL, 0);
			startcol = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--end") == 0) {
			if (i >= argc - 2)
				usage(argv[0], "--end requires position\n");
			endrow = strtol(argv[++i], NULL, 0);
			endcol = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--wall-in") == 0) {
			if (i >= argc - 2)
				usage(argv[0], "--wall-in requires position\n");
			if (wallin)
				usage(argv[0], "Multiple --wall-in commands\n");
			wallin = 1;
			wallinrow = strtol(argv[++i], NULL, 0);
			wallincol = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--nosolve") == 0) {
			solve = 0;
		} else if (strcmp(argv[i], "--clear") == 0) {
			clear = 1;
		} else if (strcmp(argv[i], "--help") == 0) {
			usage(argv[0], "");
		} else {
			int j = maze_solve_parse(i, argc, argv);

			if (i == j)
				usage(argv[0], "Unrecognized argument: %s\n",
				      argv[i]);
			i = j - 1;
		}
		i++;
	}

	/* Get maze. */
	srandom(seed);
	if (generate) {
		if (startrow < 0)
			startrow = maze_row_col_frac(rows, 1, -startrow);
		if (startcol < 0)
			startcol = maze_row_col_frac(cols, 1, -startcol);
		if (endrow < 0)
			endrow = maze_row_col_frac(rows, 1, -endrow);
		if (endcol < 0)
			endcol = maze_row_col_frac(cols, 1, -endcol);
		mp = maze_create(rows, cols, startrow, startcol,
				 straightfrac, segbends, revisit);
	} else if (binin != NULL) {
		mp = maze_binary_in(binin);
		if (mp == NULL)
			usage(argv[0], "Bad --input file\n");
		if (clear)
			maze_unvisit_all(mp);
		if (startrow < 0)
			startrow = maze_row_col_frac(mp->nrows, 1, -startrow);
		if (startcol < 0)
			startcol = maze_row_col_frac(mp->ncols, 1, -startcol);
		if (endrow < 0)
			endrow = maze_row_col_frac(mp->nrows, 1, -endrow);
		if (endcol < 0)
			endcol = maze_row_col_frac(mp->ncols, 1, -endcol);
	} else {
		usage(argv[0], "Must specify one of --input and --generate\n");
	}
	if (startrow == endrow && startcol == endcol)
		usage(argv[0], "--start and --end both (%d, %d)\n",
		      startrow, startcol);

	/* Wall-in the specified cell. */
	if (wallin) {
		if (wallinrow < 0)
			wallinrow = maze_row_col_frac(mp->nrows, 1, -wallinrow);
		if (wallincol < 0)
			wallincol = maze_row_col_frac(mp->ncols, 1, -wallincol);
		if (!maze_wall_in(mp, wallinrow, wallincol))
			usage(argv[0],
			      "--wall-in %d %d must be within maze, "
			      "limits: %d %d.\n",
			      wallinrow, wallincol, mp->nrows, mp->ncols);
	}

	/* Solve maze. */
	if (solve) {
		maze_unvisit_all(mp);  /* Erase any prior solution. */
		if (!maze_cell_exists(mp, startrow, startcol)) {
			fprintf(stderr,
				"Start position %d %d must be within maze: "
				"(0-%d, 0-%d)\n",
				startrow, startcol,
				mp->nrows - 1, mp->ncols - 1);
			exit(EXIT_FAILURE);
		}
		if (!maze_cell_exists(mp, endrow, endcol)) {
			fprintf(stderr,
				"End position %d %d must be within maze: "
				"(0-%d, 0-%d)\n",
				endrow, endcol, mp->nrows - 1, mp->ncols - 1);
			exit(EXIT_FAILURE);
		}
		q = maze_solve(mp, startrow, startcol, endrow, endcol, &dt);
		if (q == 0) {
			fprintf(stderr, "Maze has no solution\n");
			solved = 0;
		}
		q = q / (double)(abs(endrow - startrow) +
				 abs(endcol - startcol) + 1);
		fprintf(stderr,
			"Maze quality: %g  dt = %g visits = %d/%d (%g%%)\n",
			q, ((double)dt) / (double)1000000, mp->vi,
			mp->nrows * mp->ncols,
			mp->vi * 100. / (double)(mp->nrows * mp->ncols));
	}

	/* Output binary, if requested. */
	if (binout != NULL)
		maze_binary_out(binout, mp);

	/* Output fig, if requested. */
	if (figfp != NULL) {
		if (!figupcgiven) {  /* Set up for US Letter. */
			int fr = 300 * 41 / mp->nrows;
			int fc = 300 * 32 / mp->ncols;

			if (fr < fc)
				figupc = fr;
			else
				figupc = fc;
		}
		maze_to_fig(figfp, mp, figupc, !solved || figvisit);
	}

	return EXIT_SUCCESS;
}
