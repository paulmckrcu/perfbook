/*
 * Test the SC scenario as follows:
 *
 *	P0:     x=1; hwsync; y=1;
 *	P1:     y=2; hwsync; z=1;
 *	P2:     z=2; hwsync; v=1;
 *	P3:     r1=v; hwsync; r2=x;
 *
 *	assert(!(y==2&&z==2&&r1==1&&r2==0)) after all done.
 *	r1->a, r2->a1
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
		state.y = 1; \
		hwsync(); \
		while (state.f > 0) \
			barrier(); \
		hwsync(); \
		if (state.y == 2 && state.z == 2 && \
		    state.a == 1 && state.a1 == 0) { \
		    	state.badcount++; \
			break; \
		} \
	} while (0)

#define THREAD_1 \
	do { \
		state.y = 2; \
		hwsync(); \
		state.z = 1; \
	} while (0)

#define THREAD_2 \
	do { \
		state.z = 2; \
		hwsync(); \
		state.v = 1; \
	} while (0)

#define THREAD_3 \
	do { \
		state.a = state.v; \
		hwsync(); \
		state.a1 = state.x; \
	} while (0)

/* #define THREAD_4 */

/* #define THREAD_5 */

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 0, &state.a },
	{ 1, &state.y },
	{ 2, &state.z },
	{ 2, &state.v },
	{ 3, &state.x },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0 /* 0 */, thread_0 },
	{ 1 /* 2 */, thread_1 },
	{ 2 /* 4 */, thread_2 },
	{ 3 /* 6 */, thread_3 },
	{-1, NULL },
};
