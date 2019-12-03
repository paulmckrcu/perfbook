/*
 * Sleepable Read-Copy Update mechanism for mutual exclusion
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
 * Copyright (C) IBM Corporation, 2006-2019
 * Copyright (C) Facebook, 2019
 *
 * Author: Paul McKenney <paulmck@us.ibm.com>
 *
 * For detailed explanation of Read-Copy Update mechanism see -
 * 		Documentation/RCU/ *.txt
 *
 */

#ifndef _LINUX_SRCU_H
#define _LINUX_SRCU_H

#include <urcu.h>

struct srcu_struct_array {
	int c[2];
};

struct srcu_struct {
	int completed;
	DEFINE_PER_THREAD(struct srcu_struct_array, per_thread_count);
	spinlock_t mutex;
};

void cleanup_srcu_struct(struct srcu_struct *sp);
int __srcu_read_lock(struct srcu_struct *sp);
void __srcu_read_unlock(struct srcu_struct *sp, int idx);
void synchronize_srcu(struct srcu_struct *sp);
void synchronize_srcu_expedited(struct srcu_struct *sp);
long srcu_batches_completed(struct srcu_struct *sp);

/**
 * srcu_read_lock - register a new reader for an SRCU-protected structure.
 * @sp: srcu_struct in which to register the new reader.
 *
 * Enter an SRCU read-side critical section.  Note that SRCU read-side
 * critical sections may be nested.  However, it is illegal to
 * call anything that waits on an SRCU grace period for the same
 * srcu_struct, whether directly or indirectly.  Please note that
 * one way to indirectly wait on an SRCU grace period is to acquire
 * a mutex that is held elsewhere while calling synchronize_srcu() or
 * synchronize_srcu_expedited().
 */
static inline int srcu_read_lock(struct srcu_struct *sp)
{
	return __srcu_read_lock(sp);
}

/**
 * srcu_read_unlock - unregister a old reader from an SRCU-protected structure.
 * @sp: srcu_struct in which to unregister the old reader.
 * @idx: return value from corresponding srcu_read_lock().
 *
 * Exit an SRCU read-side critical section.
 */
static inline void srcu_read_unlock(struct srcu_struct *sp, int idx)
{
	__srcu_read_unlock(sp, idx);
}

#endif
