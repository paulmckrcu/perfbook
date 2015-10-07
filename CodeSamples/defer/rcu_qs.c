/*
 * rcu_qs.c: user-level implementation of Classic RCU, eliminating all
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

#include "../api.h"
#include "rcu_qs.h"

void synchronize_rcu(void)
{
	int t;

	/* Memory barrier ensures mutation seen before grace period. */

	smp_mb();

	/* Only one synchronize_rcu() at a time. */

	spin_lock(&rcu_gp_lock);

	/* Advance to a new grace-period number, enforce ordering. */

	rcu_gp_ctr += 2;
	smp_mb();

	/*
	 * Wait until all threads are either out of their RCU read-side
	 * critical sections or are aware of the new grace period.
	 */

	for_each_thread(t) {
		while (rcu_gp_ongoing(t) &&
		       ((per_thread(rcu_reader_qs_gp, t) - rcu_gp_ctr) < 0)) {
			/* @@@ poll(NULL, 0, 10); */
			barrier();
		}
	}

	/* Let other synchronize_rcu() instances move ahead. */

	spin_unlock(&rcu_gp_lock);

	/* Ensure that any subsequent free()s happen -after- above checks. */

	smp_mb();
}

#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
