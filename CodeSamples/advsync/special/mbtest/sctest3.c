/*
 * sctest3.c: Three-variable independent-write/independent-read test.
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
		while (state.f > 0) \
			barrier(); \
		hwsync(); \
		if (state.a1 == 1 && /* T1.y */ \
		    state.a == 0 &&  /* T1.x */ \
		    state.b == 1 &&  /* T3.x */ \
		    state.b1 == 0) { /* T3.y */ \
			state.badcount++; \
			break; \
		} \
		if (state.a2 == 1 && /* T1.z */ \
		    state.a == 0 &&  /* T1.x */ \
		    state.b == 1 &&  /* T3.x */ \
		    state.b2 == 0) { /* T3.z */\
			state.badcount++; \
			break; \
		} \
		if (state.a2 == 1 && /* T1.z */ \
		    state.a1 == 0 && /* T1.y */ \
		    state.b1 == 1 && /* T3.y */ \
		    state.b2 == 0) { /* T3.z */ \
			state.badcount++; \
			break; \
		} \
	} while (0)

#define THREAD_1 \
	do { \
		state.a2 = state.z; \
		hwsync(); \
		state.a1 = state.y; \
		hwsync(); \
		state.a = state.x; \
	} while (0)

#define THREAD_2 \
	do { \
		state.y = 1; \
	} while (0)

#define THREAD_3 \
	do { \
		state.b = state.x; \
		hwsync(); \
		state.b1 = state.y; \
		hwsync(); \
		state.b2 = state.z; \
	} while (0)

#define THREAD_4 \
	do { \
		state.z = 1; \
	} while (0)

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 1, &state.a },
	{ 3, &state.b },
	{ 3, &state.x },
	{ 1, &state.y },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ /* 0 */ 0, thread_0 },
	{ /* 1 */ 2, thread_1 },
	{ /* 2 */ 4, thread_2 },
	{ /* 3 */ 6, thread_3 },
	{ /* 4 */ 8, thread_4 },
	{-1, NULL },
};
