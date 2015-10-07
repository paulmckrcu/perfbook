/*
 * Test the SC scenario as follows:
 *
 *	P0:     x=1; hwsync; r1=y;
 *	P1:     r2=y; hwsync; r3=z;
 *	P2:     r4=z; hwsync; v=1;
 *	P3:     r5=v; hwsync; r6=x;
 *	P4:     y=1;
 *	P5:     z=1;
 *
 *	assert(!(r1==0&&r2==1&&r3==0&&r4=1&&r5==1&&r6==0)) after all done.
 *	r1->a, r2->b, r3->b1, r4->c, r5->d, r6->d1
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
		state.a = state.y; \
		hwsync(); \
		while (state.f > 0) \
			barrier(); \
		hwsync(); \
		if (state.a == 0 && state.b == 1 && \
		    state.b1 == 0 && state.c == 1 && \
		    state.d == 1 && state.d1 == 0) { \
		    	state.badcount++; \
			break; \
		} \
	} while (0)

#define THREAD_1 \
	do { \
		state.b = state.y; \
		hwsync(); \
		state.b1 = state.z; \
	} while (0)

#define THREAD_2 \
	do { \
		state.c = state.z; \
		hwsync(); \
		state.v = 1; \
	} while (0)

#define THREAD_3 \
	do { \
		state.d = state.v; \
		hwsync(); \
		state.d1 = state.x; \
	} while (0)

#define THREAD_4 \
	do { \
		state.y = 1; \
	} while (0)

#define THREAD_5 \
	do { \
		state.z = 1; \
	} while (0)

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 0, &state.a },
	{ 1, &state.y },
	{ 1, &state.b },
	{ 2, &state.z },
	{ 2, &state.c },
	{ 2, &state.v },
	{ 3, &state.x },
	{ 3, &state.d },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0 /* 0 */, thread_0 },
	{ 1 /* 2 */, thread_1 },
	{ 2 /* 4 */, thread_2 },
	{ 3 /* 6 */, thread_3 },
	{ 4 /* 8 */, thread_4 },
	{ 5 /* 10 */, thread_5 },
	{-1, NULL },
};
