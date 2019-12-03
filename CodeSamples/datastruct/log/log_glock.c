/*
 * log_glock.c: Simple log protected by single global lock.  This global lock
 *	is the log_head's ->lh_lock.
 *
 * Usage:
 *
 *	./log_glock --smoketest
 *		Run a simple single-threaded smoke test.
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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "log.h"

/*
 * Initialize a log_head structure with the specified number of records.
 */
void log_init(struct log_head *lp, long nrecs)
{
	lp->lh_log = calloc(sizeof(*lp->lh_log), nrecs);
	if (!lp->lh_log)
		abort();
	lp->lh_n_entries = nrecs;
	spin_lock_init(&lp->lh_lock);
	lp->lh_next_idx = 0;
}

/*
 * Clean up a log_head structure, preferably after everyone is done using it.
 */
void log_cleanup(struct log_head *lp)
{
	free(lp->lh_log);
}

/*
 * Return the value logged at the specified index.  Note that memory
 * ordering was enforced when "idx" was fetched/created.
 */
unsigned long get_log_value(struct log_head *lp, long idx)
{
	if (idx >= READ_ONCE(lp->lh_next_idx))
		abort();
	return lp->lh_log[idx].lr_value;
}

/*
 * Append the specified value to the log, returning the corresponding
 * index.  As long as this index is used by the current thread or is
 * passed in a synchronized manner to some other thread, it may be
 * passed to get_log_value().
 */
long log_append(struct log_head *lp, unsigned long val)
{
	long ret;

	spin_lock(&lp->lh_lock);
	if (lp->lh_next_idx >= lp->lh_n_entries)
		abort();
	ret = lp->lh_next_idx;
	WRITE_ONCE(lp->lh_log[ret].lr_value, val);
	smp_mb();  /* Order .lr_value write against later ret accesses. */
	WRITE_ONCE(lp->lh_next_idx, ret + 1);
	spin_unlock(&lp->lh_lock);
	return ret;
}

/*
 * Return the current next-slot index.  This can be used to validate
 * log indexes, for example, for debug checks rejecting indexes greater
 * than or equal to the value returned.
 */
long get_log_next_idx(struct log_head *lp)
{
	/* Ensure that later calls to get_log_value() see earlier data. */
	return smp_load_acquire(&lp->lh_next_idx);
}

#ifdef TEST_LOG
#include "logtorture.h"
#endif /* #ifdef TEST_LOG */
