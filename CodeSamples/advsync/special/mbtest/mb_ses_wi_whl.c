/*
 * mb_ses_wi_whl.c: Another ornate load-store chain.
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
		eieio(); \
		state.b = 1; \
	} while (0)

#define THREAD_1 \
	do { \
		if (state.b == 1) { \
			barrier(); \
			state.b++; \
			break; \
		} \
	} while (1)

#define THREAD_2 \
	do { \
		if (state.b == 2) { \
			hwsync(); \
			if (state.a == 0) \
				state.badcount++; \
			break; \
		} \
	} while (1)

/* #define THREAD_3 */
/* #define THREAD_4 */

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 0, &state.b },
	{ 1, &state.c },
	{ 2, &state.a },
	{-2, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0, thread_0 },
	{ 1, thread_1 },
	{ 2, thread_2 },
	{-1, NULL },
};
