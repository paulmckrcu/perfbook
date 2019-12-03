/*
 * rcu_lock_percpu.c: simple user-level implementation of RCU based on
 * per-CPU locking.
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
#include "rcu_lock_percpu.h"

//\begin{snippet}[labelbase=ln:defer:rcu_lock_percpu:sync,commandchars=\\\[\]]
void synchronize_rcu(void)
{
	int t;

	for_each_running_thread(t) {		//\lnlbl{loop:b}
		spin_lock(&per_thread(rcu_gp_lock, t));
		spin_unlock(&per_thread(rcu_gp_lock, t));
	}					//\lnlbl{loop:e}
}
//\end{snippet}

#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
