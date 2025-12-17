/*
 * rcu_rcl.c: simple user-level implementation of RCU based on per-thread
 * pairs of global reference counters.
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
#include "rcu_rcl.h"

//\begin{snippet}[labelbase=ln:defer:rcu_rcl:u,gobbleblank=yes,commandchars=\\\@\$]
void synchronize_rcu(void)
{
	int t;
						//\fcvblank
	smp_mb();				//\lnlbl{sync:mb1}
	spin_lock(&rcu_gp_lock);
	for_each_thread(t) {			//\lnlbl{sync:loop:b}
		while (per_thread(rcu_nesting, t) != 0) {
#ifndef FCV_SNIPPET
			barrier();
#else
			poll(NULL, 0, 10);
#endif
		}
	}					//\lnlbl{sync:loop:e}
	spin_unlock(&rcu_gp_lock);
	smp_mb();				//\lnlbl{sync:mb2}
}
//\end{snippet}

#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
