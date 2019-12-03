/*
 * rcu_nest32.c: user-level implementation of RCU permitting nesting,
 * 	adapted for 32-bit systems.
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
#include "rcu_nest32.h"

static void flip_counter_and_wait(void)
{
	int t;

	/* Advance to a new grace-period number, enforce ordering. */

	rcu_gp_ctr ^= RCU_GP_CTR_BOTTOM_BIT;
	smp_mb();

	/*
	 * Wait until all threads are either out of their RCU read-side
	 * critical sections or are aware of the new grace period.
	 */

	for_each_thread(t) {
		while (rcu_old_gp_ongoing(t)) {
			/*@@@ poll(NULL, 0, 10); */
			barrier();
		}
	}
}

void synchronize_rcu(void)
{
	/* Memory barrier ensures mutation seen before grace period. */

	smp_mb();

	/* Only one synchronize_rcu() at a time. */

	spin_lock(&rcu_gp_lock);

	/*
	 * Flip the counter once and wait for old readers to go away,
	 * but someone might have been preempted while we waited, so
	 * we must flip and wait twice.
	 */

	flip_counter_and_wait();
	barrier();
	flip_counter_and_wait();

	/* Let other synchronize_rcu() instances move ahead. */

	spin_unlock(&rcu_gp_lock);

	/* Ensure that any subsequent free()s happen -after- above checks. */

	smp_mb();
}

#ifdef TEST
#define RCU_READ_NESTABLE
#include "rcutorture.h"
#endif /* #ifdef TEST */
