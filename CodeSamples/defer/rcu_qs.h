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
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "rcu_pointer.h"

//\begin{snippet}[labelbase=ln:defer:rcu_qs:define,commandchars=\\\[\]]
DEFINE_SPINLOCK(rcu_gp_lock);
long rcu_gp_ctr = 0;	/* increment by RCU_GP_CTR_BOTTOM_BIT each gp. */
DEFINE_PER_THREAD(long, rcu_reader_qs_gp);
//\end{snippet}

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

//\begin{snippet}[labelbase=ln:defer:rcu_qs:read_lock_unlock,gobbleblank=yes,commandchars=\%\@\$]
static void rcu_read_lock(void)			//\lnlbl{lock:b}
{
}
							//\fcvblank
static void rcu_read_unlock(void)
{
}						//\lnlbl{unlock:e}
							//\fcvblank
static void rcu_quiescent_state(void)		//\lnlbl{qs:b}
{
	smp_mb();				//\lnlbl{qs:mb1}
	__get_thread_var(rcu_reader_qs_gp) =	//\lnlbl{qs:gp1}
		READ_ONCE(rcu_gp_ctr) + 1;	//\lnlbl{qs:gp2}
	smp_mb();				//\lnlbl{qs:mb2}
}						//\lnlbl{qs:e}
							//\fcvblank
static void rcu_thread_offline(void)		//\lnlbl{offline:b}
{
	smp_mb();				//\lnlbl{offline:mb1}
	__get_thread_var(rcu_reader_qs_gp) =	//\lnlbl{offline:gp1}
		READ_ONCE(rcu_gp_ctr);		//\lnlbl{offline:gp2}
	smp_mb();				//\lnlbl{offline:mb2}
}						//\lnlbl{offline:e}
							//\fcvblank
static void rcu_thread_online(void)		//\lnlbl{online:b}
{
	rcu_quiescent_state();			//\lnlbl{online:qs}
}						//\lnlbl{online:e}
//\end{snippet}

extern void synchronize_rcu(void);
