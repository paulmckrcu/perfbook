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
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

//\begin{snippet}[labelbase=ln:count:count_stat:inc-read,commandchars=\\\[\]]
DEFINE_PER_THREAD(unsigned long, counter);		//\lnlbl{define}

static __inline__ void inc_count(void)			//\lnlbl{inc:b}
{
	unsigned long *p_counter = &__get_thread_var(counter);

	WRITE_ONCE(*p_counter, *p_counter + 1);
}							//\lnlbl{inc:e}

static __inline__ unsigned long read_count(void)	//\lnlbl{read:b}
{
	int t;
	unsigned long sum = 0;

	for_each_thread(t)
		sum += READ_ONCE(per_thread(counter, t));
	return sum;
}							//\lnlbl{read:e}
//\end{snippet}

void count_init(void)
{
}

void count_cleanup(void)
{
}

#include "counttorture.h"
