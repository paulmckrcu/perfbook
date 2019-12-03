/*
 * rcu_lock.h: simple user-level implementation of RCU based on locking.
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

DEFINE_SPINLOCK(rcu_gp_lock);

static void rcu_init(void)
{
}

//\begin{snippet}[labelbase=ln:defer:rcu_lock:lock_unlock,commandchars=\\\[\]]
static void rcu_read_lock(void)
{
	spin_lock(&rcu_gp_lock);
}

static void rcu_read_unlock(void)
{
	spin_unlock(&rcu_gp_lock);
}
//\end{snippet}

extern void synchronize_rcu(void);
