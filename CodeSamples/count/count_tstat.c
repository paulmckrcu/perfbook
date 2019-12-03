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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

//\begin{snippet}[labelbase=ln:count:count_tstat:whole,keepcomment=yes,commandchars=\\\@\$]
unsigned long __thread counter = 0;
unsigned long *counterp[NR_THREADS] = { NULL };
int finalthreadcount = 0;
DEFINE_SPINLOCK(final_mutex);

static __inline__ void inc_count(void)
{
	WRITE_ONCE(counter, counter + 1);
}

static __inline__ unsigned long read_count(void)
                  /* need to tweak counttorture! */
{
	int t;
	unsigned long sum = 0;

	for_each_thread(t)
		if (READ_ONCE(counterp[t]) != NULL)
			sum += READ_ONCE(*counterp[t]);
	return sum;
}

#ifndef FCV_SNIPPET
void count_init(void)
{
}
#endif /* FCV_SNIPPET */
				//\fcvexclude
void count_register_thread(unsigned long *p)
{
	WRITE_ONCE(counterp[smp_thread_id()], &counter);
}

void count_unregister_thread(int nthreadsexpected)
{
	spin_lock(&final_mutex);
	finalthreadcount++;
	spin_unlock(&final_mutex);
	while (READ_ONCE(finalthreadcount) < nthreadsexpected)
		poll(NULL, 0, 1);
}
//\end{snippet}

void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#define KEEP_GCC_THREAD_LOCAL
#include "counttorture.h"
