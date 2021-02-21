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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../defer/rcu_nest32.c"
#include <string.h>

//\begin{snippet}[labelbase=ln:count:count_end_rcu:whole,commandchars=\%\@\$]
struct countarray {				//\lnlbl{struct:b}
	unsigned long total;
	unsigned long *counterp[NR_THREADS];
};						//\lnlbl{struct:e}

unsigned long __thread counter = 0;		//\lnlbl{perthread:b}
struct countarray *countarrayp = NULL;
DEFINE_SPINLOCK(final_mutex);			//\lnlbl{perthread:e}

__inline__ void inc_count(void)			//\lnlbl{inc:b}
{
	WRITE_ONCE(counter, counter + 1);
}						//\lnlbl{inc:e}

unsigned long read_count(void)			//\lnlbl{read:b}
{
	struct countarray *cap;
	unsigned long *ctrp;
	unsigned long sum;
	int t;

	rcu_read_lock();			//\lnlbl{read:rrl}
	cap = rcu_dereference(countarrayp);	//\lnlbl{read:deref}
	sum = READ_ONCE(cap->total);		//\lnlbl{read:init}
	for_each_thread(t) {			//\lnlbl{read:add:b}
		ctrp = READ_ONCE(cap->counterp[t]);
		if (ctrp != NULL) sum += *ctrp;	//\lnlbl{read:add:e}
	}
	rcu_read_unlock();			//\lnlbl{read:rru}
	return sum;				//\lnlbl{read:ret}
}						//\lnlbl{read:e}

void count_init(void)				//\lnlbl{init:b}
{
	countarrayp = malloc(sizeof(*countarrayp));
	if (countarrayp == NULL) {
		fprintf(stderr, "Out of memory\n");
		exit(EXIT_FAILURE);
	}
	memset(countarrayp, '\0', sizeof(*countarrayp));
}						//\lnlbl{init:e}

void count_register_thread(unsigned long *p)	//\lnlbl{reg:b}
{
	int idx = smp_thread_id();		//\lnlbl{reg:idx}

	spin_lock(&final_mutex);		//\lnlbl{reg:acq}
	countarrayp->counterp[idx] = &counter;  //\lnlbl{reg:set}
	spin_unlock(&final_mutex);		//\lnlbl{reg:rel}
}						//\lnlbl{reg:e}

void count_unregister_thread(int nthreadsexpected)	//\lnlbl{unreg:b}
{
	struct countarray *cap;
	struct countarray *capold;
	int idx = smp_thread_id();

	cap = malloc(sizeof(*countarrayp));		//\lnlbl{unreg:alloc:b}
	if (cap == NULL) {
		fprintf(stderr, "Out of memory\n");
		exit(EXIT_FAILURE);
	}						//\lnlbl{unreg:alloc:e}
	spin_lock(&final_mutex);			//\lnlbl{unreg:acq}
	*cap = *countarrayp;				//\lnlbl{unreg:copy}
	WRITE_ONCE(cap->total, cap->total + counter);	//\lnlbl{unreg:add}
	cap->counterp[idx] = NULL;			//\lnlbl{unreg:null}
	capold = countarrayp;				//\lnlbl{unreg:retain}
	rcu_assign_pointer(countarrayp, cap);		//\lnlbl{unreg:assign}
	spin_unlock(&final_mutex);			//\lnlbl{unreg:rel}
	synchronize_rcu();				//\lnlbl{unreg:sync}
	free(capold);					//\lnlbl{unreg:free}
}							//\lnlbl{unreg:e}
//\end{snippet}

__inline__ void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "counttorture.h"
