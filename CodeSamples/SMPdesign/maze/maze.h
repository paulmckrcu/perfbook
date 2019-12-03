/*
 * maze.h: headers for simple maze create/solve program.
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

#ifndef __MAZE_H__
#define __MAZE_H__

#define ABORT() \
	do { \
		fprintf(stderr, "Aborted at %s:%d\n", __FILE__, __LINE__); \
		abort(); \
	} while (0)

#define MAZE_CONTINUE_SEGMENT 0
#define MAZE_STUCK_SEGMENT    1
#define MAZE_END_SEGMENT      2

/* Bitmap for maze cell. */
#define WALL_UP    0x80000000
#define WALL_DOWN  0x40000000
#define WALL_RIGHT 0x20000000
#define WALL_LEFT  0x10000000
#define VISITED    0x08000000
#define SOLUTION   0x04000000
#define COOKIE     0x03ffffff  /* Distance or thread ID, depending. */
typedef int cell_t;

#ifndef CELL_PAD_SIZE
#define CELL_PAD_SIZE 0
#endif

/* Optional padding for cache-line alignment. */
struct cell {
	cell_t c;
	char pad[CELL_PAD_SIZE];
};

/* Segment weights for maze-creation random path choice. */
struct segment_weights {
	double contweight; /* continue current direction. */
	double randweight; /* randomly turn right or left. */
	/* 1.0 for stopweight. */
};

/* Represent a row/column pair. */
struct rowcol {
	int row;
	int col;
};

/* Maze representation. */
static char bin_file_header[] = "Maze0.1";  /* For binary file formats. */
struct maze {
	int nrows;
	int ncols;
	struct segment_weights weights[2];
	struct rowcol *visited;
	int vi;
	int lastvi;
	double revisit;
	struct maze_solve_private *msp;
	struct cell cell[0];
};

#define ACCESS_ONCE(x) (*(volatile typeof(x) *)&(x))
#define READ_ONCE(x) \
            ({ typeof(x) ___x = ACCESS_ONCE(x); ___x; })
#define WRITE_ONCE(x, val) ({ ACCESS_ONCE(x) = (val); })


/* CLOCK_MONOTONIC_RAW prefered, but the older CLOCK_MONOTONIC will do. */
#ifdef CLOCK_MONOTONIC_RAW
#define MAZE_CLOCK CLOCK_MONOTONIC_RAW
#else /* #ifdef CLOCK_MONOTONIC_RAW */
#define MAZE_CLOCK CLOCK_MONOTONIC
#endif /* #else #ifdef CLOCK_MONOTONIC_RAW */

/* Is the specified cell actually within the boundaries of the maze? */
static inline int maze_cell_exists(struct maze *mp, int row, int col)
{
	return row >= 0 && row < mp->nrows && col >= 0 && col < mp->ncols;
}

/* Return address of bitmask for specified cell.  Numbered from zero. */
static inline cell_t *maze_get_cell_addr(struct maze *mp, int row, int col)
{
	if (!maze_cell_exists(mp, row, col))
		ABORT();
	return &mp->cell[row * mp->ncols + col].c;
}

/* Return contents of bitmask for specified cell. */
static inline cell_t maze_get_cell(struct maze *mp, int row, int col)
{
	return *maze_get_cell_addr(mp, row, col);
}

/* Update contents of bitmask for specified cell. */
static inline void maze_set_cell(struct maze *mp, int row, int col, cell_t val)
{
	*maze_get_cell_addr(mp, row, col) = val;
}

/* Return the wall bit that prevents movement from current to other cell. */
static inline cell_t maze_find_wallbit(int currow, int curcol,
				       int otherrow, int othercol)
{
	if (currow == otherrow) {
		if (curcol - 1 == othercol)
			return WALL_LEFT;
		else if (curcol + 1 == othercol)
			return WALL_RIGHT;
		else
			ABORT();
	} else if (currow - 1 == otherrow)
		return WALL_UP;
	else if (currow + 1 == otherrow)
		return WALL_DOWN;
	else
		ABORT();
}

/* Are the two cells adjacent and connected? */
static inline int maze_cells_connected(struct maze *mp,
				       int row1, int col1, int row2, int col2)
{
	if (abs(row1 - row2) + abs(col1 - col2) != 1)
		ABORT();
	if (!maze_cell_exists(mp, row1, col1) ||
	    !maze_cell_exists(mp, row2, col2))
	    	return 0;
	return (maze_find_wallbit(row1, col1, row2, col2) &
		maze_get_cell(mp, row1, col1)) == 0;
}

unsigned long long current_time(void);
int maze_raw_col_frac(int rc, int num, int den);
void maze_set_seg_weights(struct segment_weights *swp,
			  int len, double straightfrac, double segbends);
struct maze *new_empty_maze(int nrows, int ncols,
			    double straightfrac, double segbends,
			    double revisit);
void maze_to_fig(FILE * fp, struct maze *mp, int upc, int visited);
double drandom(void);
int pmrandom(void);
int maze_cell_visited(struct maze *mp, int row, int col);
void maze_visit_cell(struct maze *mp, int row, int col, int distance);
int maze_find_any_next_cell(struct maze *mp, int cr, int cc, int *nr, int *nc);
void maze_build_one_cell_wall(struct maze *mp, int wallrow, int wallcol,
			      int prevrow, int prevcol, int currow, int curcol,
			      int nextrow, int nextcol);
void maze_build_cell_walls(struct maze *mp, int prevrow, int prevcol,
			   int currow, int curcol, int nextrow, int nextcol);
int maze_choose_next_cell(struct maze *mp, int prevrow, int prevcol,
			  int currow, int curcol, int *nextrow, int *nextcol);
int maze_wall_in(struct maze *mp, int row, int col);
void maze_construct_segment(struct maze *mp, int row1, int col1,
			    int row2, int col2);
void maze_remove_wall(struct maze *mp, int currow, int curcol,
		      int otherrow, int othercol);
int maze_find_boundary(struct maze *mp, int *prevrow, int *prevcol,
		       int *currow, int *curcol);
void maze_unvisit_all(struct maze *mp);
struct maze *maze_create(int nrows, int ncols, int startrow, int startcol,
			 double straightfrac, double segbends, double revisit);
int maze_is_prev_cell(struct maze *mp, int row1, int col1, int row2, int col2,
		      int *nextrow, int *nextcol);
int maze_mark_solution(struct maze *mp, int startrow, int startcol,
			int endrow, int endcol);
int maze_binary_out(char *path, struct maze *mp);
struct maze *maze_binary_in(char *path);

/* Maze-solver API. */
cell_t maze_get_cell_distance(struct maze *mp, int row, int col);
void maze_set_cell_distance(struct maze *mp, int tr, int tc, int distance);
cell_t maze_get_cell_tid(struct maze *mp, int row, int col);
int maze_same_tids(struct maze *mp, int r1, int c1, int r2, int c2);
void new_empty_maze_solve(struct maze *mp);
int maze_try_visit_cell(struct maze *mp, int cr, int cc, int tr, int tc,
			int *nextrow, int *nextcol, int distance);
int maze_row_col_frac(int rc, int num, int den);
int maze_solve(struct maze *mp, int startrow, int startcol,
	       int endrow, int endcol, unsigned long long *t);
void usage(char *progname, const char *format, ...);
void maze_solve_usage(void);
int maze_solve_parse(int i, int argc, char *argv[]);

#endif /* #ifndef __MAZE_H__ */
