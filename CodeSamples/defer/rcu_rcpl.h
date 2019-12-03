/*
 * rcu_rcpl.h: simple user-level implementation of RCU based on per-thread
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

#include "rcu_pointer.h"

//\begin{snippet}[labelbase=ln:defer:rcu_rcpl:define,commandchars=\\\@\$]
DEFINE_SPINLOCK(rcu_gp_lock);
DEFINE_PER_THREAD(int [2], rcu_refcnt);
atomic_t rcu_idx;
DEFINE_PER_THREAD(int, rcu_nesting);
DEFINE_PER_THREAD(int, rcu_read_idx);
//\end{snippet}

static void rcu_init(void)
{
	int t;

	atomic_set(&rcu_idx, 0);
	init_per_thread(rcu_nesting, 0);
	for_each_thread(t) {
		per_thread(rcu_refcnt, t)[0] = 0;
		per_thread(rcu_refcnt, t)[1] = 0;
	}
}

//\begin{snippet}[labelbase=ln:defer:rcu_rcpl:r,commandchars=\\\@\$]
static void rcu_read_lock(void)
{
	int i;
	int n;

	n = __get_thread_var(rcu_nesting);
	if (n == 0) {
		i = atomic_read(&rcu_idx);
		__get_thread_var(rcu_read_idx) = i;
		__get_thread_var(rcu_refcnt)[i]++;
	}
	__get_thread_var(rcu_nesting) = n + 1;
	smp_mb();
}

static void rcu_read_unlock(void)
{
	int i;
	int n;

	smp_mb();
	n = __get_thread_var(rcu_nesting);
	if (n == 1) {
		i = __get_thread_var(rcu_read_idx);
		__get_thread_var(rcu_refcnt)[i]--;
	}
	__get_thread_var(rcu_nesting) = n - 1;
}
//\end{snippet}

extern void synchronize_rcu(void);
