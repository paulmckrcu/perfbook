/*
 * MoreThanOneValue-15CPU.c: Convert memory order 15 CPU result into .fig
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
 * Copyright (c) 2016 Akira Yokosawa
 */

#include <stdio.h>
#include <stdlib.h>

#define CPU_NUM (15)
#define MAX_CHANGE (15)
#define TIM_WIDTH_UPPER (15)
#define TIM_WIDTH_LOWER (150)
#define MAX_TIME_UPPER (550)
#define MAX_TIME_LOWER (50)
#define RULER_TICK_UPPER (50)
#define RULER_TICK_LOWER (5)
#define DIAGRAM_NUM (2)

const struct diagram_param_s {
    int fig_base;
    int tim_width;
    int max_time;
    int fig_width;
    int bar_height;
    int ruler_tick;
} diag_param[DIAGRAM_NUM] = {
    {700, TIM_WIDTH_UPPER, MAX_TIME_UPPER, MAX_TIME_UPPER * TIM_WIDTH_UPPER,
     270, RULER_TICK_UPPER * TIM_WIDTH_UPPER},
    {700, TIM_WIDTH_LOWER, MAX_TIME_LOWER, MAX_TIME_LOWER * TIM_WIDTH_LOWER,
     270, RULER_TICK_LOWER * TIM_WIDTH_LOWER}
};

struct color_table_s {
    int col[CPU_NUM];
    int fill[CPU_NUM];
    int col_norsp[CPU_NUM];
    int fill_norsp[CPU_NUM];
};

/* local storage for value change */
static int chg_time[CPU_NUM][MAX_CHANGE];
static int chg_val[CPU_NUM][MAX_CHANGE];
static int unresp_time_b[CPU_NUM][MAX_CHANGE];
static int unresp_time_e[CPU_NUM][MAX_CHANGE];

int draw_diagram(int n, int m, const struct color_table_s *col_table, int y_offset)
{
    int fig_base = diag_param[n].fig_base;
    int max_time = diag_param[n].max_time;
    int tim_width = diag_param[n].tim_width;
    int fig_width = diag_param[n].fig_width;
    int bar_height = diag_param[n].bar_height;
    int ruler_tick = diag_param[n].ruler_tick;
    int i, j, k;
    int next_time;
    int unresp_end;

    /* output boxes for each CPU */
    for (i = 0; i < CPU_NUM; i++) {
	printf("2 2 0 1 0 0 50 0 12 0.000 0 0 -1 0 0 5\n");
	printf("\t%d %d %d %d %d %d %d %d %d %d\n",
	       fig_base, bar_height * i + y_offset,
	       fig_base + chg_time[i][0] * tim_width, bar_height * i + y_offset,
	       fig_base + chg_time[i][0] * tim_width, bar_height * (i + 1) + y_offset,
	       fig_base, bar_height * (i + 1) + y_offset,
	       fig_base, bar_height * i + y_offset
	       );
	for (j = 0; j < MAX_CHANGE; j++) {
	    next_time = chg_time[i][j+1];
	    if (next_time == 0 || next_time >= max_time)
		next_time = max_time;
	    printf("2 2 0 1 0 %d 50 0 %d 0.000 0 0 -1 0 0 5\n",
		   col_table[m].col[chg_val[i][j]-1], col_table[m].fill[chg_val[i][j]-1]);
	    printf("\t%d %d %d %d %d %d %d %d %d %d\n",
		   fig_base + chg_time[i][j] * tim_width, bar_height * i + y_offset,
		   fig_base + next_time * tim_width, bar_height * i + y_offset,
		   fig_base + next_time * tim_width, bar_height * (i + 1) + y_offset,
		   fig_base + chg_time[i][j] * tim_width, bar_height * (i + 1) + y_offset,
		   fig_base + chg_time[i][j] * tim_width, bar_height * i + y_offset
		);

	    for (k = 0; k < MAX_CHANGE; k++) {
		if (unresp_time_b[i][k] == 0 || unresp_time_e[i][k] == 0)
		    break;
		if (unresp_time_b[i][k] > chg_time[i][j] &&
		    unresp_time_b[i][k] < next_time) {
		    /* let's draw */
		    unresp_end = unresp_time_e[i][k];
		    if (unresp_end >= max_time)
			unresp_end = max_time;
		    printf("2 2 0 0 0 %d 50 0 %d 0.000 0 0 -1 0 0 5\n",
			   col_table[m].col_norsp[chg_val[i][j]-1],
			   col_table[m].fill_norsp[chg_val[i][j]-1]
			);
		    printf("\t%d %d %d %d %d %d %d %d %d %d\n",
			   fig_base + unresp_time_b[i][k] * tim_width,
			   bar_height * i + 200 + y_offset,
			   fig_base + unresp_end * tim_width - 10,
			   bar_height * i + 200 + y_offset,
			   fig_base + unresp_end * tim_width - 10,
			   bar_height * (i + 1) - 10 + y_offset,
			   fig_base + unresp_time_b[i][k] * tim_width,
			   bar_height * (i + 1) - 10 + y_offset,
			   fig_base + unresp_time_b[i][k] * tim_width,
			   bar_height * i + 200 + y_offset
			);
		}
	    }

	    printf("4 1 0 50 0 18 9 0.0000 4 90 150 %d %d %d\\001\n",
		   fig_base + (chg_time[i][j] + next_time) / 2 * tim_width,
		   bar_height * i + 200 + y_offset, chg_val[i][j]);
	    if (chg_time[i][j+1] == 0 || chg_time[i][j+1] >= max_time) break;
	}
    }
    /* output ruler */
    /* horiz line */
    printf("2 1 0 2 0 7 50 0 -1 0.000 0 0 -1 1 0 2\n");
    printf("\t1 1 1.00 60.00 120.00\n");
    printf("\t %d %d %d %d\n", fig_base, bar_height * CPU_NUM + 200 + y_offset,
	   fig_base + max_time * tim_width, bar_height * CPU_NUM + 200 + y_offset);
    /* ruler ticks */
    i = 0;
    do {
	printf("2 1 0 1 0 7 50 0 -1 0.000 0 0 -1 0 0 2\n");
	printf("\t %d %d %d %d\n",
	       fig_base + ruler_tick * i, bar_height * CPU_NUM + 150 + y_offset,
	       fig_base + ruler_tick * i, bar_height * CPU_NUM + 250 + y_offset);
	printf("4 1 0 50 0 16 9 0.0000 4 90 375 %d %d %d\\001\n",
	       fig_base + ruler_tick * i, bar_height * CPU_NUM + 400 + y_offset,
	       (ruler_tick * i)/tim_width);
	i++;
    } while (ruler_tick * i < fig_width);
    /* label CPU */
    for (i = 0; i < CPU_NUM; i++) {
	printf("4 2 0 50 0 16 8.5 0.0000 4 105 420 %d %d CPU %2d\\001\n",
	       fig_base - 30, bar_height * i + 200 + y_offset, i + 1);
    }
    return 0;
}

int main(void)
{
    int i, j, k;
    int ret;
    int mode;
    int mode_num;
    int fig_base;
    int fig_width;
    int bar_height;
    struct color_table_s *color_table;

    /* read mode */
    ret = scanf("%d ", &mode);
    if (EOF == ret)
	goto err_exit;
    ret = scanf("%d ", &mode_num);
    if (EOF == ret)
	goto err_exit;
    if (mode >= mode_num)
	goto err_exit;
    /* read color selection data for given mode_num */
    /* first, allocate memory */
    color_table = calloc(mode_num, sizeof(struct color_table_s));
    if (NULL == color_table) {
	fprintf(stderr, "memory allocation failed for color_table\n");
	return 1;
    }
    /* read color param */
    for (i = 0; i < mode_num; i++) {
	for (j = 0; j < CPU_NUM; j++) {
	    ret = scanf("%d ", &color_table[i].col[j]);
	    if (EOF == ret)
		goto err_exit;
	}
	for (j = 0; j < CPU_NUM; j++) {
	    ret = scanf("%d ", &color_table[i].fill[j]);
	    if (EOF == ret)
		goto err_exit;
	}
	for (j = 0; j < CPU_NUM; j++) {
	    ret = scanf("%d ", &color_table[i].col_norsp[j]);
	    if (EOF == ret)
		goto err_exit;	
	}
	for (j = 0; j < CPU_NUM; j++) {
	    ret = scanf("%d ", &color_table[i].fill_norsp[j]);
	    if (EOF == ret)
		goto err_exit;
	}
	ret = scanf("%d ", &k);
	if (EOF == ret)
	    goto err_exit;
	if (999 != k) {
	    fprintf(stderr, "read: %d, expeced 999\n", k);
	    goto err_exit;
	}
    }
    /* read value change data from stdin */
    for (i = 0; i < CPU_NUM; i++) {
	for (j = 0; j < MAX_CHANGE; j++) {
	    ret = scanf("%d ", &chg_time[i][j]);
	    if (EOF == ret)
		goto err_exit;
	    ret = scanf("%d ", &chg_val[i][j]);
	    if (EOF == ret)
		goto err_exit;
	    if (chg_time[i][j] == 0 || chg_val[i][j] == 0)
		break;
	}
	for (j = 0; j < MAX_CHANGE; j++) {
	    ret = scanf("%d ", &unresp_time_b[i][j]);
	    if (EOF == ret)
		goto err_exit;
	    ret = scanf("%d ", &unresp_time_e[i][j]);
	    if (EOF == ret)
		goto err_exit;
	    if (unresp_time_b[i][j] == 0 || unresp_time_e[i][j] == 0)
		break;
	}
    }
    /* output preamble */
    printf("#FIG 3.2\n");
    printf("Landscape\n");
    printf("Center\n");
    printf("Metric\n");
    printf("A4\n");
    printf("100.00\n");
    printf("Single\n");
    printf("-2\n");
    printf("1200 2\n");
    /* draw upper diagram */
    fig_base = diag_param[0].fig_base;
    fig_width = diag_param[0].fig_width;
    bar_height = diag_param[0].bar_height;
    printf("6 %d 0 %d %d\n", fig_base - 50, fig_base + fig_width + 50,
	   (bar_height * CPU_NUM) + 100);
    ret = draw_diagram(0, mode, color_table, 0);
    printf("-6\n");
    if (ret != 0)
	goto err_exit;
    /* draw lower diagrem */
    fig_base = diag_param[1].fig_base;
    fig_width = diag_param[1].fig_width;
    bar_height = diag_param[1].bar_height;
    printf("6 %d 4860 %d %d\n", fig_base - 50, fig_base + fig_width + 50 -205,
	   (bar_height * CPU_NUM) + 100 + 5165);
    ret = draw_diagram(1, mode, color_table, 4860);
    printf("-6\n");
    if (ret != 0)
	goto err_exit;
    /* draw some lines */
    printf("2 1 1 1 0 7 50 -1 -1 4.000 0 0 -1 0 0 2\n");
    printf("\t%d %d %d %d\n", fig_base, 4250, fig_base, 4860);
    printf("2 1 1 1 0 7 50 -1 -1 4.000 0 0 -1 0 0 2\n");
    printf("\t%d %d %d %d\n", fig_base + 750, 4250, 8200, 4860);
    printf("2 1 0 1 0 7 50 -1 -1 4.000 0 0 -1 0 0 2\n");
    printf("\t%d %d %d %d\n", 3900, 4725, 3900, 9270);

    return 0;

err_exit:
    fprintf(stderr, "error in input\n");
    return 1;
}
