/*
 * rcu_sig.c: signal-based implementation of RCU, using approach similar
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

#include "../api.h"
#include "rcu_sig.h"

static void urcu_sig_handler(int unused)
{
	if (urcu_state.urcu_qs != URCU_QS_REQ)
		return;
	smp_mb();
	if (ACCESS_ONCE(urcu_state.urcu_nesting) != 0)
		urcu_state.urcu_qs = URCU_QS_ACK;
	else
		urcu_state.urcu_qs = URCU_QS_DONE;
}

void synchronize_rcu(void)
{
	struct urcu_state *p;
	int t;
	thread_id_t tid;

	/* Memory barrier ensures mutation seen before grace period. */

	smp_mb();

	/* Only one synchronize_rcu() at a time. */

	spin_lock(&rcu_gp_lock);

	/* Request a quiescent state from each thread. */

	for_each_tid(t, tid) {
		p = per_thread(urcu_statep, t);
		if (p != NULL) {
			p->urcu_qs = URCU_QS_REQ;
			pthread_kill(tid, SIGUSR1);
		}
	}

	/*
	 * Wait until all threads have exited any RCU read-side critical
	 * sections that they were once in.
	 */

	for_each_tid(t, tid) {
		p = per_thread(urcu_statep, t);
		if (p == NULL)
			continue;
		while (p->urcu_qs != URCU_QS_DONE) {
			poll(NULL, 0, 1);
			if (p->urcu_qs == URCU_QS_REQ)
				pthread_kill(tid, SIGUSR1);
		}
		p->urcu_qs = URCU_QS_IDLE;
	}

	/* Let other synchronize_rcu() instances move ahead. */

	spin_unlock(&rcu_gp_lock);

	/* Ensure that any subsequent free()s happen -after- above checks. */

	smp_mb();
}

void rcu_init(void)
{
	struct sigaction sa;

	init_per_thread(urcu_statep, NULL);
	sa.sa_handler = urcu_sig_handler;
	sigemptyset(&sa.sa_mask);
	sa.sa_flags = 0;
	if (sigaction(SIGUSR1, &sa, NULL) != 0) {
		perror("sigaction");
		exit(EXIT_FAILURE);
	}
}

void rcu_register_thread(void)
{
	spin_lock(&rcu_gp_lock);
	__get_thread_var(urcu_statep) = &urcu_state;
	spin_unlock(&rcu_gp_lock);
}

void rcu_unregister_thread(void)
{
	spin_lock(&rcu_gp_lock);
	__get_thread_var(urcu_statep) = NULL;
	spin_unlock(&rcu_gp_lock);
}

#ifdef TEST
#define NEED_REGISTER_THREAD
#include "rcutorture.h"
#endif /* #ifdef TEST */
