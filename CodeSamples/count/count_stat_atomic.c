/*
 * count_stat_atomic.c: Per-thread atomic statistical counters.
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

DEFINE_PER_THREAD(atomic_t, counter);

void inc_count(void)
{
	atomic_inc(&__get_thread_var(counter));
}

__inline__ unsigned long read_count(void)
{
	int t;
	unsigned long sum = 0;

	for_each_thread(t)
		sum += atomic_read(&per_thread(counter, t));
	return sum;
}

__inline__ void count_init(void)
{
}

__inline__ void count_cleanup(void)
{
}

#include "counttorture.h"
