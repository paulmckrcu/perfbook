/*
 * mb_s_lis_shl.c: Yet another ornate load-store chain.
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
		state.x = 1; \
	} while (0)

#define THREAD_1 \
	do { \
		/* cisync(&state.x, &state.a); */ \
		state.a = state.x; \
		cisync(state.a); \
		state.a1 = state.y; \
		hwsync(); \
		state.d1 = 1; \
		hwsync(); \
	} while (0)

#define THREAD_2 \
	do { \
		state.y = 1; \
		hwsync(); \
		state.b = state.x; \
		hwsync(); \
		state.d = 1; \
		hwsync(); \
		while (state.d1 != 1) \
			barrier(); \
		hwsync(); \
		if (state.a == 1 &&  \
		    state.a1 == 0 && \
		    state.b == 0) {  \
			state.badcount++; \
			break; \
		} \
	} while (0)

/* #define THREAD_3 */

/* #define THREAD_4 */

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 1, &state.a },
	{ 2, &state.b },
	{ 2, &state.x },
	{ 1, &state.y },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0 /* 0 */, thread_0 },
	{ 1 /* 2 */, thread_1 },
	{ 2 /* 4 */, thread_2 },
	{-1, NULL },
};
