/*
 * count_end.c: Per-thread statistical counters that provide sum at end.
 *	Uses __thread for each thread's counter.
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"

unsigned long __thread counter = 0;
unsigned long *counterp[NR_THREADS] = { NULL };
unsigned long finalcount = 0;
DEFINE_SPINLOCK(final_mutex);

void inc_count(void)
{
	counter++;
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

void count_init(void)
{
}

void count_register_thread(void)
{
	int idx = smp_thread_id();

	spin_lock(&final_mutex);
	counterp[idx] = &counter;
	spin_unlock(&final_mutex);
}

void count_unregister_thread(int nthreadsexpected)
{
	int idx = smp_thread_id();

	spin_lock(&final_mutex);
	finalcount += counter;
	counterp[idx] = NULL;
	spin_unlock(&final_mutex);
}

#define NEED_REGISTER_THREAD
#include "counttorture.h"
