/*
 * Test Peter Dimov's counterexample to Anthony's example.
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
		hwsync(); \
		state.y = 2; \
		while (state.f > 0) \
			barrier(); \
		hwsync(); \
		if (state.a1 == 2 && state.a2 == 1 && \
		    state.b1 == 2 && state.b2 == 1) { \
			state.anomalies++; \
			break; \
		} \
	} while (0)

#define THREAD_1 \
	do { \
		state.y = 1; \
		hwsync(); \
		state.x = 2; \
	} while (0)

#define THREAD_2 \
	do { \
		state.a1 = state.x; \
		cisync(state.a1); \
		state.a2 = state.x; \
	} while (0)

#define THREAD_3 \
	do { \
		state.b1 = state.y; \
		cisync(state.b1); \
		state.b2 = state.y; \
	} while (0)

/* #define THREAD_4 */

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 0, &state.x },
	{ 1, &state.y },
	{ 2, &state.a },
	{ 3, &state.b },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0 /* 0 */, thread_0 },
	{ 2 /* 2 */, thread_1 },
	{ 1 /* 4 */, thread_2 },
	{ 3 /* 6 */, thread_3 },
	{-1, NULL },
};
