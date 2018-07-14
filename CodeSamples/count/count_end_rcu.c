/*
 * count_end_rcu.c: Per-thread statistical counters that provide sum at end.
 *	Uses __thread for each thread's counter.  Use RCU to synchronize
 *	with task exit.
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

#include "../defer/rcu_nest32.c"
#include <string.h>

struct countarray {
	unsigned long total;
	unsigned long *counterp[NR_THREADS];
};

unsigned long __thread counter = 0;
struct countarray *countarrayp = NULL;
DEFINE_SPINLOCK(final_mutex);

void inc_count(void)
{
	counter++;
}

unsigned long read_count(void)
{
	struct countarray *cap;
	unsigned long sum;
	int t;

	rcu_read_lock();
	cap = rcu_dereference(countarrayp);
	sum = cap->total;
	for_each_thread(t)
		if (cap->counterp[t] != NULL)
			sum += *cap->counterp[t];
	rcu_read_unlock();
	return sum;
}

void count_init(void)
{
	countarrayp = malloc(sizeof(*countarrayp));
	if (countarrayp == NULL) {
		fprintf(stderr, "Out of memory\n");
		exit(EXIT_FAILURE);
	}
	memset(countarrayp, '\0', sizeof(*countarrayp));
}

void count_register_thread(unsigned long *p)
{
	int idx = smp_thread_id();

	spin_lock(&final_mutex);
	countarrayp->counterp[idx] = &counter;
	spin_unlock(&final_mutex);
}

void count_unregister_thread(int nthreadsexpected)
{
	struct countarray *cap;
	struct countarray *capold;
	int idx = smp_thread_id();

	cap = malloc(sizeof(*countarrayp));
	if (cap == NULL) {
		fprintf(stderr, "Out of memory\n");
		exit(EXIT_FAILURE);
	}
	spin_lock(&final_mutex);
	*cap = *countarrayp;
	cap->total += counter;
	cap->counterp[idx] = NULL;
	capold = countarrayp;
	rcu_assign_pointer(countarrayp, cap);
	spin_unlock(&final_mutex);
	synchronize_rcu();
	free(capold);
}

void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "counttorture.h"
