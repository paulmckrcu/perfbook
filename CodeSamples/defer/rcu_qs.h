/*
 * rcu_qs.h: user-level implementation of Classic RCU, eliminating all
 * read-side memory barriers, while still permitting threads to block
 * indefinitely outside of an RCU read-side critical section without
 * also blocking grace periods, as long as the last RCU read-side critical
 * section is followed by a call to rcu_thread_offline().  A call to
 * rcu_thread_online() must appear between a call to rcu_thread_offline()
 * and the next RCU read-side critical section.
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
long rcu_gp_ctr = 0;	/* increment by RCU_GP_CTR_BOTTOM_BIT each gp. */
DEFINE_PER_THREAD(long, rcu_reader_qs_gp);

#define mark_rcu_quiescent_state() rcu_quiescent_state()
#define put_thread_offline() rcu_thread_offline()
#define put_thread_online() rcu_thread_online()

static inline int rcu_gp_ongoing(int thread)
{
	return per_thread(rcu_reader_qs_gp, thread) & 1;
}

/*
 * Note: threads must invoke rcu_thread_online() before their
 * first RCU read-side critical section.
 */
static void rcu_init(void)
{
	init_per_thread(rcu_reader_qs_gp, rcu_gp_ctr);
}

static void rcu_read_lock(void)
{
}

static void rcu_read_unlock(void)
{
}

static void rcu_quiescent_state(void)
{
	smp_mb();
	__get_thread_var(rcu_reader_qs_gp) = ACCESS_ONCE(rcu_gp_ctr) + 1;
	smp_mb();
}

static void rcu_thread_offline(void)
{
	smp_mb();
	__get_thread_var(rcu_reader_qs_gp) = ACCESS_ONCE(rcu_gp_ctr);
	smp_mb();
}

static void rcu_thread_online(void)
{
	rcu_quiescent_state();
}

extern void synchronize_rcu(void);
