/*
 * mb_sbs_lbl.c: One thread does a pair of stores, the other loads the
 *	same variables in opposite order, with barriers in both cases.
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
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

#define THREAD_0 \
	do { \
		state.a = 1; \
		lwsync(); \
		state.b = 1; \
		while (state.f > 0) \
			barrier(); \
		if (state.y == 1 && state.x == 0) { \
			state.badcount++; \
			break; \
		} \
	} while (0)

#define THREAD_1 \
	do { \
		state.y = state.b; \
		lwsync(); \
		state.x = state.a; \
	} while (0)

/* #define THREAD_2 */
/* #define THREAD_3 */
/* #define THREAD_4 */

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 0, &state.b },
	{ 1, &state.a },
	{ 1, &state.x },
	{ 1, &state.y },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0, thread_0 },
	{ 1, thread_1 },
	{-1, NULL },
};
