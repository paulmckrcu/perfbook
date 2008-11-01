/*
 * rcu_rcpg.c: simple user-level implementation of RCU based on a single
 * pair of global reference counter.
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"
#include "rcu_rcpg.h"

void synchronize_rcu(void)
{
	smp_mb();
	spin_lock(&rcu_gp_lock);

	/* Flip counter once and wait for old counts to go away. */

	atomic_set(&rcu_idx, !atomic_read(&rcu_idx));
	smp_mb();
	while (atomic_read(&rcu_refcnt[!atomic_read(&rcu_idx)]) != 0) {
		/* @@@ poll(NULL, 0, 10); */
	}

	/*
	 * But someone might have been preempted while we waited, so
	 * we must flip and wait one more time.
	 */

	atomic_set(&rcu_idx, !atomic_read(&rcu_idx));
	smp_mb();
	while (atomic_read(&rcu_refcnt[!atomic_read(&rcu_idx)]) != 0) {
		/* @@@ poll(NULL, 0, 10); */
	}
	spin_unlock(&rcu_gp_lock);
	smp_mb();
}

#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
