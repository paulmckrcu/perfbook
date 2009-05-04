/*
 * count_stat.c: Per-thread statistical counters.
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

long __thread counter = 0;
long *counterp[NR_THREADS] = { NULL };
long finalcount = 0;
DEFINE_SPINLOCK(final_mutex);

void inc_count(void)
{
	counter++;
}

long read_count(void)
{
	int t;
	long sum = finalcount;

	spin_lock(&final_mutex);
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
	counterp[smp_thread_id()] = &counter;
}

void count_unregister_thread(void)
{
	spin_lock(&final_mutex);
	finalcount += counter;
	counterp[smp_thread_id()] = NULL;
	spin_unlock(&final_mutex);
}

#define NEED_REGISTER_THREAD
#include "counttorture.h"
