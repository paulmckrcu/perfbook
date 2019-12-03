/*
 * count_stack.c: Per-thread statistical counters that provide sum at end.
 *	Uses on-stack variable for each thread's counter.
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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

unsigned long __thread *counter = NULL;
unsigned long *counterp[NR_THREADS] = { NULL };
unsigned long finalcount = 0;
DEFINE_SPINLOCK(final_mutex);

__inline__ void inc_count(void)
{
	WRITE_ONCE(*counter,
		   READ_ONCE(*counter) + 1);
}

unsigned long read_count(void)
{
	int t;
	unsigned long sum;

	spin_lock(&final_mutex);
	sum = finalcount;
	for_each_thread(t)
		if (counterp[t] != NULL)
			sum += *counterp[t];
	spin_unlock(&final_mutex);
	return sum;
}

__inline__ void count_init(void)
{
}

void count_register_thread(unsigned long *p)
{
	int idx = smp_thread_id();

	spin_lock(&final_mutex);
	counterp[idx] = p;
	counter = p;
	spin_unlock(&final_mutex);
}

void count_unregister_thread(int nthreadsexpected)
{
	int idx = smp_thread_id();

	spin_lock(&final_mutex);
	finalcount += *counter;
	counterp[idx] = NULL;
	spin_unlock(&final_mutex);
}

__inline__ void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "counttorture.h"
