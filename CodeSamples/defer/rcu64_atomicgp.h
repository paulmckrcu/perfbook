/*
 * rcu64_atomicgp.h: simple user-level implementation of RCU leveraging large
 *	counter that is safe from overflow, and that uses atomic instructions
 *	to avoid lock contention from multiple concurrent updates.
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

DEFINE_PER_THREAD(long, rcu_reader_gp);

/*
 * This counter must be large enough to never decrement to 0.
 * In theory, could start from -LONG_MAX and increment, but on twos-comp
 * machines you must -not- start from LONG_MIN and increment, as this
 * would cause integer overflow for any rcu_read_lock() calls that are
 * so unfortunate as to be invoked before the first synchronize_rcu().
 */

long rcu_gp_ctr = LONG_MAX;

static void rcu_init(void)
{
	init_per_thread(rcu_reader_gp, 0);
}

static void rcu_read_lock(void)
{
	/*
	 * Copy the current GP counter to this thread's counter,
	 * negating it to indicate that it is in an RCU read-side 
	 * critical section.  Do a memory barrier to keep the critical
	 * section penned in.  (Dropping the memory barrier requires
	 * periodic per-thread processing.)
	 */

	__get_thread_var(rcu_reader_gp) = -rcu_gp_ctr;
	smp_mb();
}

static void rcu_read_unlock(void)
{
	/*
	 * Copy the current GP counter to this thread's counter, but
	 * keeping the same sign to indicate that it is no longer
	 * in an RCU read-side critical section.  (As before, dropping
	 * the memory barrier requires periodic per-thread processing.)
	 */

	smp_mb();
	__get_thread_var(rcu_reader_gp) = rcu_gp_ctr;
}

extern void synchronize_rcu(void);
