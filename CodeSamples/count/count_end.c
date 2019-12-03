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
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

//\begin{snippet}[labelbase=ln:count:count_end:whole,commandchars=\\\@\$]
unsigned long __thread counter = 0;		//\lnlbl{var:b}
unsigned long *counterp[NR_THREADS] = { NULL };
unsigned long finalcount = 0;
DEFINE_SPINLOCK(final_mutex);			//\lnlbl{var:e}

static __inline__ void inc_count(void)		//\lnlbl{inc:b}
{
	WRITE_ONCE(counter, counter + 1);
}						//\lnlbl{inc:e}

static __inline__ unsigned long read_count(void)
{
	int t;
	unsigned long sum;

	spin_lock(&final_mutex);			//\lnlbl{read:acquire}
	sum = finalcount;				//\lnlbl{read:sum:init}
	for_each_thread(t)				//\lnlbl{read:loop:b}
		if (counterp[t] != NULL)		//\lnlbl{read:check}
			sum += READ_ONCE(*counterp[t]);	//\lnlbl{read:loop:e}
	spin_unlock(&final_mutex);			//\lnlbl{read:release}
	return sum;					//\lnlbl{read:return}
}

#ifndef FCV_SNIPPET
__inline__ void count_init(void)
{
}
#endif /* FCV_SNIPPET */
						//\fcvexclude
void count_register_thread(unsigned long *p)	//\lnlbl{reg:b}
{
	int idx = smp_thread_id();

	spin_lock(&final_mutex);
	counterp[idx] = &counter;
	spin_unlock(&final_mutex);
}						//\lnlbl{reg:e}

void count_unregister_thread(int nthreadsexpected)	//\lnlbl{unreg:b}
{
	int idx = smp_thread_id();

	spin_lock(&final_mutex);			//\lnlbl{unreg:acquire}
	finalcount += counter;				//\lnlbl{unreg:add}
	counterp[idx] = NULL;				//\lnlbl{unreg:NULL}
	spin_unlock(&final_mutex);			//\lnlbl{unreg:release}
}							//\lnlbl{unreg:e}
//\end{snippet}

__inline__ void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "counttorture.h"
