/*
 * rcu_sig.h: signal-based implementation of RCU, using approach similar
 *	to that of TREE_PREEMPT_RCU in the Linux kernel.
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
#include <signal.h>

DEFINE_SPINLOCK(rcu_gp_lock);

#define URCU_QS_IDLE	-1	/* No grace period in progress. */
#define	URCU_QS_REQ	0	/* Requesting quiescent state from thread. */
#define URCU_QS_ACK	1	/* Request acknowledged, need unlock. */
#define	URCU_QS_DONE	2	/* Quiescent state done. */

struct urcu_state {
	int		urcu_nesting;
	sig_atomic_t	urcu_qs;
};
struct urcu_state __thread urcu_state = { .urcu_qs = URCU_QS_IDLE };
DEFINE_PER_THREAD(struct urcu_state *, urcu_statep);

static void rcu_read_lock(void)
{
	urcu_state.urcu_nesting++;
	barrier();
}

static void rcu_read_unlock(void)
{
	barrier();
	if (likely(--urcu_state.urcu_nesting == 0) &&
	    unlikely(urcu_state.urcu_qs >= URCU_QS_ACK)) {
		smp_mb();
		urcu_state.urcu_qs = URCU_QS_DONE;
	}
}

extern void synchronize_rcu(void);
extern void rcu_init(void);
