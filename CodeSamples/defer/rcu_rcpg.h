/*
 * rcu_rcpg.h: simple user-level implementation of RCU based on a single
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

#include "rcu_pointer.h"

//\begin{snippet}[labelbase=ln:defer:rcu_rcpg:define,commandchars=\\\@\$]
DEFINE_SPINLOCK(rcu_gp_lock);
atomic_t rcu_refcnt[2];
atomic_t rcu_idx;
DEFINE_PER_THREAD(int, rcu_nesting);
DEFINE_PER_THREAD(int, rcu_read_idx);
//\end{snippet}

static void rcu_init(void)
{
	atomic_set(&rcu_refcnt[0], 0);
	atomic_set(&rcu_refcnt[1], 0);
	atomic_set(&rcu_idx, 0);
	init_per_thread(rcu_nesting, 0);
}

//\begin{snippet}[labelbase=ln:defer:rcu_rcpg:r,commandchars=\\\@\$]
static void rcu_read_lock(void)
{
	int i;
	int n;

	n = __get_thread_var(rcu_nesting);		//\lnlbl{lock:pick}
	if (n == 0) {					//\lnlbl{lock:if}
		i = atomic_read(&rcu_idx);		//\lnlbl{lock:cur:b}
		__get_thread_var(rcu_read_idx) = i;	//\lnlbl{lock:set}
		atomic_inc(&rcu_refcnt[i]);		//\lnlbl{lock:cur:e}
	}
	__get_thread_var(rcu_nesting) = n + 1;		//\lnlbl{lock:inc}
	smp_mb();					//\lnlbl{lock:mb}
}

static void rcu_read_unlock(void)
{
	int i;
	int n;

	smp_mb();					//\lnlbl{unlock:mb}
	n = __get_thread_var(rcu_nesting);		//\lnlbl{unlock:nest}
	if (n == 1) {					//\lnlbl{unlock:if}
		i = __get_thread_var(rcu_read_idx);	//\lnlbl{unlock:idx}
		atomic_dec(&rcu_refcnt[i]);		//\lnlbl{unlock:atmdec}
	}
	__get_thread_var(rcu_nesting) = n - 1;		//\lnlbl{unlock:decnest}
}
//\end{snippet}

extern void synchronize_rcu(void);
