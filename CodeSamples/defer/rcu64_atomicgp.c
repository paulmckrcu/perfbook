/*
 * rcu64_atomicgp.c: simple user-level implementation of RCU leveraging large
 *	counter that is safe from overflow, but with concurrent update
 *	processing based on atomic instructions.
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
#include "rcu64_atomicgp.h"

void synchronize_rcu(void)
{
	int t;
	long oldval;

	/* Memory barrier ensures mutation seen before grace period. */

	smp_mb();

	/*
	 * Atomically advance to a new grace-period number, enforce ordering.
	 * Failure is OK -- someone will have advanced the grace-period
	 * number for use.
	 */

	oldval = rcu_gp_ctr;
	(void)cmpxchg(&rcu_gp_ctr, oldval, oldval - 1);
	smp_mb();

	/*
	 * Wait until all threads are either out of their RCU read-side
	 * critical sections or are aware of the new grace period.
	 */

	for_each_thread(t) {
		while (per_thread(rcu_reader_gp, t) <= -oldval) {
			/*@@@ poll(NULL, 0, 10); */
			barrier();
		}
	}

	/* Ensure that any subsequent free()s happen -after- above checks. */

	smp_mb();
}

#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
