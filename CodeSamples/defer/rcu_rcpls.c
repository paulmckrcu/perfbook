/*
 * rcu_rcpls.c: simple user-level implementation of RCU based on per-thread
 * pairs of global reference counters, but that is also capable of sharing
 * grace periods between multiple updates.
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
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include "rcu_rcpls.h"

//\begin{snippet}[labelbase=ln:defer:rcu_rcpls:u,gobbleblank=yes,commandchars=\\\@\$]
static void flip_counter_and_wait(int ctr)
{
	int i;
	int t;
							//\fcvblank
	WRITE_ONCE(rcu_idx, ctr + 1);			//\lnlbl{flip:inc}
	i = ctr & 0x1;					//\lnlbl{flip:mask}
	smp_mb();
	for_each_thread(t) {
		while (per_thread(rcu_refcnt, t)[i] != 0) {
#ifndef FCV_SNIPPET
			barrier();
#else
			poll(NULL, 0, 10);
#endif
		}
	}
	smp_mb();
}
						//\fcvblank
void synchronize_rcu(void)
{
	int ctr;
	int oldctr;				//\lnlbl{sync:oldctr}
						//\fcvblank
	smp_mb();
	oldctr = READ_ONCE(rcu_idx);		//\lnlbl{sync:idx}
	smp_mb();				//\lnlbl{sync:mb2}
	spin_lock(&rcu_gp_lock);
	ctr = READ_ONCE(rcu_idx);
	if (ctr - oldctr >= 3) {		//\lnlbl{sync:if:b}

		/*
		 * There have been at least two full cycles, so
		 * all pre-existing RCU read-side critical sections
		 * must have completed.  Our work is done!
		 */

		spin_unlock(&rcu_gp_lock);
		smp_mb();
		return;				//\lnlbl{sync:ret}
	}					//\lnlbl{sync:if:e}

	/*
	 * Flip counter once and wait for old counts to go away,
	 * but someone might have been preempted while we waited, so
	 * we must flip and wait twice.  Unless a pair of flips happened
	 * while we were acquiring the lock...
	 */

	flip_counter_and_wait(ctr);
	if (ctr - oldctr < 2)			//\lnlbl{sync:ifpair}
		flip_counter_and_wait(ctr + 1);	//\lnlbl{sync:flip2}

	spin_unlock(&rcu_gp_lock);
	smp_mb();
}
//\end{snippet}

#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
