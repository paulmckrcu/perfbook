/*
 * rcu.h: simple user-level implementation of RCU.
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
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

#include "rcu_pointer.h"

DEFINE_SPINLOCK(rcu_gp_lock);
long rcu_gp_ctr = 0;	/* always even, +=2 at start of each grace period. */
DEFINE_PER_THREAD(long, rcu_reader_gp);
DEFINE_PER_THREAD(long, rcu_reader_gp_snap);

static inline void rcu_init(void)
{
	init_per_thread(rcu_reader_gp, 0);
	init_per_thread(rcu_reader_gp_snap, 0);
}

static inline void rcu_read_lock(void)
{
	/*
	 * Copy the current GP counter to this thread's counter, setting
	 * the lower bit to indicate that it is in an RCU read-side 
	 * critical section.  Do a memory barrier to keep the critical
	 * section penned in.  (Dropping the memory barrier requires
	 * periodic per-thread processing.)
	 */

	__get_thread_var(rcu_reader_gp) = rcu_gp_ctr + 1;
	smp_mb();
}

static inline void rcu_read_unlock(void)
{
	/*
	 * Copy the current GP counter to this thread's counter, but
	 * leaving the lower bit clear to indicate that it is no longer
	 * in an RCU read-side critical section.  (As before, dropping
	 * the memory barrier requires periodic per-thread processing.)
	 */

	smp_mb();
	__get_thread_var(rcu_reader_gp) = rcu_gp_ctr;
}

extern void synchronize_rcu(void);
