/*
 * rcu_qs.h: user-level implementation of RCU permitting nesting and
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
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "rcu_pointer.h"

DEFINE_SPINLOCK(rcu_gp_lock);
#define RCU_GP_CTR_SHIFT 7
#define RCU_GP_CTR_BOTTOM_BIT (1 << RCU_GP_CTR_SHIFT)
#define RCU_GP_CTR_NEST_MASK (RCU_GP_CTR_BOTTOM_BIT - 1)
long rcu_gp_ctr = 0;	/* increment by RCU_GP_CTR_BOTTOM_BIT each gp. */
DEFINE_PER_THREAD(long, rcu_reader_gp);
DEFINE_PER_THREAD(long, rcu_reader_qs_gp);

#define mark_rcu_quiescent_state() rcu_quiescent_state()
#define put_thread_offline() rcu_thread_offline()
#define put_thread_online() rcu_thread_online()

static inline int rcu_gp_ongoing(int cpu)
{
	return per_thread(rcu_reader_qs_gp, cpu) & RCU_GP_CTR_NEST_MASK;
}

static void rcu_init(void)
{
	init_per_thread(rcu_reader_gp, 0);
	init_per_thread(rcu_reader_qs_gp, 0);
}

static void rcu_read_lock(void)
{
	long tmp;

	/*
	 * If this is the outermost RCU read-side critical section,
	 * copy the global grace-period counter.  In either case,
	 * increment the nesting count held in the low-order bits.
	 */

	tmp = __get_thread_var(rcu_reader_gp);
	if ((tmp & RCU_GP_CTR_NEST_MASK) == 0)
		tmp = rcu_gp_ctr;
	tmp++;
	__get_thread_var(rcu_reader_gp) = tmp;
}

static void rcu_read_unlock(void)
{

	/*
	 * Decrement the nesting counter held in the low-order bits,
	 * which had better not initially be zero.  The next quiescent
	 * state will provide the memory barrier, so we don't need one
	 * here.
	 */

#ifdef DEBUG_EXTREME
	BUG_ON((__get_thread_var(rcu_reader_gp) & RCU_GP_CTR_NEST_MASK) != 0);
#endif /* #ifdef DEBUG_EXTREME */
	__get_thread_var(rcu_reader_gp)--;
}

static void rcu_quiescent_state(void)
{
	long tmp;

	/*
	 * Need to disable signals if RCU read-side critical sections
	 * are permitted in signal handlers.
	 */

	smp_mb();
	tmp = __get_thread_var(rcu_reader_gp);
	if ((tmp & RCU_GP_CTR_NEST_MASK) == 0)
		tmp = rcu_gp_ctr + 1;
	__get_thread_var(rcu_reader_qs_gp) = tmp;
	smp_mb();
}

static void rcu_thread_offline(void)
{
	smp_mb();
	__get_thread_var(rcu_reader_qs_gp) = rcu_gp_ctr;
	smp_mb();
}

static void rcu_thread_online(void)
{
	smp_mb();
	__get_thread_var(rcu_reader_qs_gp) = rcu_gp_ctr + 1;
	smp_mb();
}

extern void synchronize_rcu(void);
