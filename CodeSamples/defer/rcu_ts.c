/*
 * rcu_ts.c: simple timestamp-based user-level implementation of RCU.
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
#include "rcu_ts.h"

void synchronize_rcu(void)
{
	int t;
	long rcu_gp_ctr;

	/* Memory barrier ensures mutation seen before grace period. */

	smp_mb();

	/* Only one synchronize_rcu() at a time. */

	spin_lock(&rcu_gp_lock);

	/*
	 * Pick up a new grace-period timestamp, clearing low-order bit,
	 * and enforcing ordering.
	 */

	rcu_gp_ctr = get_timestamp() & ~0x1;
	smp_mb();

	/*
	 * Wait until all threads are either out of their RCU read-side
	 * critical sections or are aware of the new grace period.
	 */

	for_each_thread(t) {
		while ((per_thread(rcu_reader_gp, t) & 0x1) &&
		       ((per_thread(rcu_reader_gp, t) - rcu_gp_ctr) < 0)) {
			/*@@@ poll(NULL, 0, 10); */
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
