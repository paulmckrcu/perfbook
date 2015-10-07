/*
 * count_lim_atomic.c: simple limit counter that uses atomic operations
 *	to steal from other threads.
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

atomic_t __thread counterandmax = ATOMIC_INIT(0);
unsigned long globalcountmax = 1 << 25;
unsigned long globalcount = 0;
unsigned long globalreserve = 0;
atomic_t *counterp[NR_THREADS] = { NULL };
DEFINE_SPINLOCK(gblcnt_mutex);
#define CM_BITS (sizeof(atomic_t) * 4)
#define MAX_COUNTERMAX ((1 << CM_BITS) - 1)

static void split_counterandmax_int(int cami, int *c, int *cm)
{
	*c = (cami >> CM_BITS) & MAX_COUNTERMAX;
	*cm = cami & MAX_COUNTERMAX;
}

static void split_counterandmax(atomic_t *cam, int *old, int *c, int *cm)
{
	unsigned int cami = atomic_read(cam);

	*old = cami;
	split_counterandmax_int(cami, c, cm);
}

static int merge_counterandmax(int c, int cm)
{
	unsigned int cami;

	cami = (c << CM_BITS) | cm;
	return ((int)cami);
}

static void globalize_count(void)
{
	int c;
	int cm;
	int old;

	split_counterandmax(&counterandmax, &old, &c, &cm);
	globalcount += c;
	globalreserve -= cm;
	old = merge_counterandmax(0, 0);
	atomic_set(&counterandmax, old);
}

static void flush_local_count(void)
{
	int c;
	int cm;
	int old;
	int t;
	int zero;

	if (globalreserve == 0)
		return;
	zero = merge_counterandmax(0, 0);
	for_each_thread(t)
		if (counterp[t] != NULL) {
			old = atomic_xchg(counterp[t], zero);
			split_counterandmax_int(old, &c, &cm);
			globalcount += c;
			globalreserve -= cm;
		}
}

static void balance_count(void)
{
	int c;
	int cm;
	int old;
	unsigned long limit;

	limit = globalcountmax - globalcount - globalreserve;
	limit /= num_online_threads();
	if (limit > MAX_COUNTERMAX)
		cm = MAX_COUNTERMAX;
	else
		cm = limit;
	globalreserve += cm;
	c = cm / 2;
	if (c > globalcount)
		c = globalcount;
	globalcount -= c;
	old = merge_counterandmax(c, cm);
	atomic_set(&counterandmax, old);
}

int add_count(unsigned long delta)
{
	int c;
	int cm;
	int old;
	int new;

	do {
		split_counterandmax(&counterandmax, &old, &c, &cm);
		if (delta > MAX_COUNTERMAX || c + delta > cm)
			goto slowpath;
		new = merge_counterandmax(c + delta, cm);
	} while (atomic_cmpxchg(&counterandmax, old, new) != old);
	return 1;
slowpath:
	spin_lock(&gblcnt_mutex);
	globalize_count();
	if (globalcountmax - globalcount - globalreserve < delta) {
		flush_local_count();
		if (globalcountmax - globalcount - globalreserve < delta) {
			spin_unlock(&gblcnt_mutex);
			return 0;
		}
	}
	globalcount += delta;
	balance_count();
	spin_unlock(&gblcnt_mutex);
	return 1;
}

int sub_count(unsigned long delta)
{
	int c;
	int cm;
	int old;
	int new;

	do {
		split_counterandmax(&counterandmax, &old, &c, &cm);
		if (delta > c)
			goto slowpath;
		new = merge_counterandmax(c - delta, cm);
	} while (atomic_cmpxchg(&counterandmax, old, new) != old);
	return 1;
slowpath:
	spin_lock(&gblcnt_mutex);
	globalize_count();
	if (globalcount < delta) {
		flush_local_count();
		if (globalcount < delta) {
			spin_unlock(&gblcnt_mutex);
			return 0;
		}
	}
	globalcount -= delta;
	balance_count();
	spin_unlock(&gblcnt_mutex);
	return 1;
}

unsigned long read_count(void)
{
	int c;
	int cm;
	int old;
	int t;
	unsigned long sum;

	spin_lock(&gblcnt_mutex);
	sum = globalcount;
	for_each_thread(t)
		if (counterp[t] != NULL) {
			split_counterandmax(counterp[t], &old, &c, &cm);
			sum += c;
		}
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
	counterp[idx] = &counterandmax;
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
