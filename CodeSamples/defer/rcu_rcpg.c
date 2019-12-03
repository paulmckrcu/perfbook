/*
 * rcu_rcpg.c: simple user-level implementation of RCU based on a single
 * pair of global reference counters.
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
#include "rcu_rcpg.h"

//\begin{snippet}[labelbase=ln:defer:rcu_rcpg:sync,gobbleblank=yes,commandchars=\\\@\$]
void synchronize_rcu(void)
{
	int i;
						//\fcvblank
	smp_mb();				//\lnlbl{mb1}
	spin_lock(&rcu_gp_lock);		//\lnlbl{acq}

	/* Flip counter once and wait for old counts to go away. */

	i = atomic_read(&rcu_idx);		//\lnlbl{pick}
	atomic_set(&rcu_idx, !i);		//\lnlbl{compl}
	smp_mb();				//\lnlbl{mb2}
	while (atomic_read(&rcu_refcnt[i]) != 0) {	//\lnlbl{while:b}
#ifndef FCV_SNIPPET
		barrier();
#else
		poll(NULL, 0, 10);
#endif
	}						//\lnlbl{while:e}
	smp_mb();				//\lnlbl{mb3}

	/*
	 * But someone might have been preempted while we waited, so
	 * we must flip and wait one more time.
	 */

	atomic_set(&rcu_idx, i);
	smp_mb();
	while (atomic_read(&rcu_refcnt[!i]) != 0) {
#ifndef FCV_SNIPPET
#else
		poll(NULL, 0, 10);
#endif
	}					//\lnlbl{while2:e}
	spin_unlock(&rcu_gp_lock);		//\lnlbl{rel}
	smp_mb();				//\lnlbl{mb5}
}
//\end{snippet}

#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
