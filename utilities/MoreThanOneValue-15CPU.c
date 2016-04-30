/*
 * MoreThanOneValue-15CPU.c: Convert memory order 15 CPU result into .fig
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

#define CPU_NUM (15)
#define MAX_CHANGE (15)
#define TIM_WIDTH (15)
#define MAX_TIME (550)
#define RULER_TICK (50 * TIM_WIDTH)

/* length unit is pixel in 1200 dpi */
static const int fig_base = 700;
static const int max_time = MAX_TIME;
static const int fig_width = MAX_TIME * TIM_WIDTH;
static const int bar_height = 270;

/* array for color selection for each value */
static const int color[CPU_NUM] = {
    4, 6, 31, 14, 2, 3, 16, 27, 7, 5, 29, 22, 20, 28, 12
};
static const int area_fill[CPU_NUM] = {
    25, 25, 25, 25, 25, 25, 25, 25, 15, 25, 25, 25, 25, 25, 25
};

/* local storage for value change */
static int chg_time[CPU_NUM][MAX_CHANGE];
static int chg_val[CPU_NUM][MAX_CHANGE];
static int unresp_time_b[CPU_NUM][MAX_CHANGE];
static int unresp_time_e[CPU_NUM][MAX_CHANGE];

int main(void)
{
    int i, j, k;
    int ret;
    int next_time;
    int mode;
    int unresp_end;

    /* read mode */
    ret = scanf("%d ", &mode);
    if (EOF == ret)
	goto err_exit;
    if (mode != 0 && mode != 1)
	goto err_exit;
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
    printf("6 %d 0 %d %d\n", fig_base - 50, fig_base + fig_width + 50,
	   (bar_height * CPU_NUM) + 100);

    /* output boxes for each CPU */
    for (i = 0; i < CPU_NUM; i++) {
	printf("2 2 0 1 0 0 50 0 15 0.000 0 0 -1 0 0 5\n");
	printf("\t%d %d %d %d %d %d %d %d %d %d\n",
	       fig_base, bar_height * i,
	       fig_base + chg_time[i][0] * TIM_WIDTH, bar_height * i,
	       fig_base + chg_time[i][0] * TIM_WIDTH, bar_height * (i + 1),
	       fig_base, bar_height * (i + 1),
	       fig_base, bar_height * i
	       );
	for (j = 0; j < MAX_CHANGE; j++) {
	    next_time = chg_time[i][j+1];
	    if (next_time == 0 || next_time >= MAX_TIME)
		next_time = max_time;
	    printf("2 2 0 1 0 %d 50 0 20 0.000 0 0 -1 0 0 5\n", color[chg_val[i][j]-1]);
	    printf("\t%d %d %d %d %d %d %d %d %d %d\n",
		   fig_base + chg_time[i][j] * TIM_WIDTH, bar_height * i,
		   fig_base + next_time * TIM_WIDTH, bar_height * i,
		   fig_base + next_time * TIM_WIDTH, bar_height * (i + 1),
		   fig_base + chg_time[i][j] * TIM_WIDTH, bar_height * (i + 1),
		   fig_base + chg_time[i][j] * TIM_WIDTH, bar_height * i
		   );
	    /* if mode == 1, draw box for unresponsive state if there is */
	    if (mode == 1) {
		for (k = 0; k < MAX_CHANGE; k++) {
		    if (unresp_time_b[i][k] == 0 || unresp_time_e[i][k] == 0)
			break;
		    if (unresp_time_b[i][k] > chg_time[i][j] &&
			unresp_time_b[i][k] < next_time) {
			/* let's draw */
			unresp_end = unresp_time_e[i][k];
			if (unresp_end >= MAX_TIME)
			    unresp_end = max_time;
			printf("2 2 0 0 0 %d 50 0 %d 0.000 0 0 -1 0 0 5\n",
			       color[chg_val[i][j]-1],
			       area_fill[chg_val[i][j]-1]
			    );
			printf("\t%d %d %d %d %d %d %d %d %d %d\n",
			       fig_base + unresp_time_b[i][k] * TIM_WIDTH,
			       bar_height * i + 10,
			       fig_base + unresp_end * TIM_WIDTH,
			       bar_height * i + 10,
			       fig_base + unresp_end * TIM_WIDTH,
			       bar_height * (i + 1) - 10,
			       fig_base + unresp_time_b[i][k] * TIM_WIDTH,
			       bar_height * (i + 1) - 10,
			       fig_base + unresp_time_b[i][k] * TIM_WIDTH,
			       bar_height * i + 10
			    );
		    }
		}
	    }
	    printf("4 1 0 50 0 18 9 0.0000 4 90 150 %d %d %d\\001\n",
		   fig_base + (chg_time[i][j] + next_time) / 2 * TIM_WIDTH,
		   bar_height * i + 200, chg_val[i][j]);
	    if (chg_time[i][j+1] == 0 || chg_time[i][j+1] >= MAX_TIME) break;
	}
    }
    /* output ruler */
    /* horiz line */
    printf("2 1 0 2 0 7 50 0 -1 0.000 0 0 -1 1 0 2\n");
    printf("\t1 1 1.00 60.00 120.00\n");
    printf("\t %d %d %d %d\n", fig_base, bar_height * CPU_NUM + 200,
	   fig_base + max_time * TIM_WIDTH, bar_height * CPU_NUM + 200);
    /* ruler ticks */
    i = 0;
    do {
	printf("2 1 0 1 0 7 50 0 -1 0.000 0 0 -1 0 0 2\n");
	printf("\t %d %d %d %d\n",
	       fig_base + RULER_TICK * i, bar_height * CPU_NUM + 150,
	       fig_base + RULER_TICK * i, bar_height * CPU_NUM + 250);
	printf("4 1 0 50 0 16 9 0.0000 4 90 375 %d %d %d\\001\n",
	       fig_base + RULER_TICK * i, bar_height * CPU_NUM + 400,
	       (RULER_TICK * i)/TIM_WIDTH);
	i++;
    } while (RULER_TICK * i < fig_width);
    /* label CPU */
    for (i = 0; i < CPU_NUM; i++) {
	printf("4 2 0 50 0 16 8.5 0.0000 4 105 420 %d %d CPU %2d\\001\n",
	       fig_base - 30, bar_height * i + 200, i + 1);
    }
    printf("-6\n");
    return 0;

err_exit:
    fprintf(stderr, "error in input\n");
    return 1;
}
