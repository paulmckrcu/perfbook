/*
 * count_lim.c: simple limit counter.
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

unsigned long __thread counter = 0;
unsigned long __thread countermax = 0;
unsigned long globalcountmax = 10000;
unsigned long globalcount = 0;
unsigned long globalreserve = 0;
unsigned long *counterp[NR_THREADS] = { NULL };
DEFINE_SPINLOCK(gblcnt_mutex);

static void globalize_count(void)
{
	globalcount += counter;
	counter = 0;
	globalreserve -= countermax;
	countermax = 0;
}

static void balance_count(void)
{
	unsigned long deltahi;

	deltahi = globalcountmax - globalcount - globalreserve;
	if (globalcount < deltahi)
		countermax = globalcount;
	else
		countermax = deltahi;
	countermax /= num_online_threads();
	globalreserve += countermax;
	counter = countermax / 2;
	globalcount -= counter;
}

int add_count(unsigned long delta)
{
	if (countermax - counter >= delta) {
		counter += delta;
		return 1;
	}
	spin_lock(&gblcnt_mutex);
	globalize_count();
	if (globalcountmax - globalcount - globalreserve < delta) {
		spin_unlock(&gblcnt_mutex);
		return 0;
	}
	globalcount += delta;
	balance_count();
	spin_unlock(&gblcnt_mutex);
	return 1;
}

int sub_count(unsigned long delta)
{
	if (counter >= delta) {
		counter -= delta;
		return 1;
	}
	spin_lock(&gblcnt_mutex);
	globalize_count();
	if (globalcount < delta) {
		spin_unlock(&gblcnt_mutex);
		return 0;
	}
	globalcount -= delta;
	balance_count();
	spin_unlock(&gblcnt_mutex);
	return 1;
}

unsigned long read_count(void)
{
	int t;
	unsigned long sum;

	spin_lock(&gblcnt_mutex);
	sum = globalcount;
	for_each_thread(t)
		if (counterp[t] != NULL)
			sum += *counterp[t];
	spin_unlock(&gblcnt_mutex);
	return sum;
}

void count_init(void)
{
}

void count_register_thread(void)
{
	int idx = smp_thread_id();

	spin_lock(&gblcnt_mutex);
	counterp[idx] = &counter;
	spin_unlock(&gblcnt_mutex);
}

void count_unregister_thread(int nthreadsexpected)
{
	int idx = smp_thread_id();

	spin_lock(&gblcnt_mutex);
	globalize_count();
	counterp[idx] = NULL;
	spin_unlock(&gblcnt_mutex);
}

void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "limtorture.h"
