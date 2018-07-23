/*
 * count_tstat.c: Per-thread statistical counters.  Uses __thread for
 *	the per-thread counter itself, and an array to allow access
 *	from other threads for the summation operation.
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

#include "../api.h"

unsigned long __thread counter = 0;
unsigned long *counterp[NR_THREADS] = { NULL };
int finalthreadcount = 0;
DEFINE_SPINLOCK(final_mutex);

void inc_count(void)
{
	WRITE_ONCE(counter,
		   READ_ONCE(counter) + 1);
}

unsigned long read_count(void)  /* known failure with counttorture! */
{
	int t;
	unsigned long sum = 0;

	for_each_thread(t)
		if (counterp[t] != NULL)
			sum += *counterp[t];
	return sum;
}

void count_init(void)
{
}

void count_register_thread(unsigned long *p)
{
	counterp[smp_thread_id()] = &counter;
}

void count_unregister_thread(int nthreadsexpected)
{
	spin_lock(&final_mutex);
	finalthreadcount++;
	spin_unlock(&final_mutex);
	while (finalthreadcount < nthreadsexpected)
		poll(NULL, 0, 1);
}

void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "counttorture.h"
