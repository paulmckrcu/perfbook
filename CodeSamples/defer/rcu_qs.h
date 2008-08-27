/*
 * rcu_qs.h: user-level implementation of RCU forbidding nesting, but
 * eliminating all read-side memory barriers, while still permitting
 * threads to block indefinitely outside of an RCU read-side critical
 * section without also blocking grace periods, as long as the last
 * RCU read-side critical section is followed by a quiescent state.
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

#include "rcu_pointer.h"

DEFINE_SPINLOCK(rcu_gp_lock);
long rcu_gp_ctr = 0;	/* increment by RCU_GP_CTR_BOTTOM_BIT each gp. */
DEFINE_PER_THREAD(long, rcu_reader_gp);
DEFINE_PER_THREAD(long, rcu_reader_qs_gp);

#define mark_rcu_quiescent_state() rcu_quiescent_state()
#define put_thread_offline() thread_offline()
#define put_thread_online() thread_online()

static inline int rcu_gp_ongoing(int cpu)
{
	return per_thread(rcu_reader_qs_gp, cpu) & 1;
}

static void rcu_init(void)
{
	int i;

	init_per_thread(rcu_reader_gp, 0);
	init_per_thread(rcu_reader_qs_gp, 0);
}

static void rcu_read_lock(void)
{
	long tmp;

	/*
	 * Copy the global grace-period counter and set
	 * the nesting count held in the low-order bits.
	 */

	__get_thread_var(rcu_reader_gp) = rcu_gp_ctr + 1;
}

static void rcu_read_unlock(void)
{

	/*
	 * Copy the current GP counter to this thread's counter, but
	 * leaving the lower bit clear to indicate that it is no longer
	 * in an RCU read-side critical section.
	 */

	__get_thread_var(rcu_reader_gp) = rcu_gp_ctr;
}

rcu_quiescent_state(void)
{
	long tmp;

	/*
	 * Need to disable signals if RCU read-side critical sections
	 * are permitted in signal handlers.
	 */

	smp_mb();
	tmp = __get_thread_var(rcu_reader_gp);
	if ((tmp & 1) == 0)
		tmp = rcu_gp_ctr + 1;
	__get_thread_var(rcu_reader_qs_gp) = tmp;
	smp_mb();
}

static void thread_offline(void)
{
	smp_mb();
	__get_thread_var(rcu_reader_qs_gp) = rcu_gp_ctr;
	smp_mb();
}

static void thread_online(void)
{
	smp_mb();
	__get_thread_var(rcu_reader_qs_gp) = rcu_gp_ctr + 1;
	smp_mb();
}

extern void synchronize_rcu(void);
