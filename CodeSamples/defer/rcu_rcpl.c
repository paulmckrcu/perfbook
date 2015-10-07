/*
 * rcu_rcpl.c: simple user-level implementation of RCU based on per-thread
 * pairs of global reference counters.
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

#include "../api.h"
#include "rcu_rcpl.h"

static void flip_counter_and_wait(int i)
{
	int t;

	atomic_set(&rcu_idx, !i);
	smp_mb();
	for_each_thread(t) {
		while (per_thread(rcu_refcnt, t)[i] != 0) {
			/* poll(NULL, 0, 10); */
			barrier();
		}
	}
	smp_mb();
}

void synchronize_rcu(void)
{
	int i;

	smp_mb();
	spin_lock(&rcu_gp_lock);
	i = atomic_read(&rcu_idx);

	/*
	 * Flip counter once and wait for old counts to go away,
	 * but someone might have been preempted while we waited, so
	 * we must flip and wait twice.
	 */

	flip_counter_and_wait(i);
	flip_counter_and_wait(!i);

	spin_unlock(&rcu_gp_lock);
	smp_mb();
}

#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
