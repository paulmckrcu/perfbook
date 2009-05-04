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

DEFINE_PER_THREAD(long, counter);

void inc_count(void)
{
	__get_thread_var(counter)++;
}

long read_count(void)
{
	int t;
	long sum = 0;

	for_each_thread(t)
		sum += per_thread(counter, t);
	return sum;
}

void count_init(void)
{
}

#include "counttorture.h"
