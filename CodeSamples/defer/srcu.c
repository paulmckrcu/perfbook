/*
 * Sleepable Read-Copy Update mechanism for mutual exclusion.
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

#include "srcu.h"

/**
 * init_srcu_struct - initialize a sleep-RCU structure
 * @sp: structure to initialize.
 *
 * Must invoke this on a given srcu_struct before passing that srcu_struct
 * to any other function.  Each srcu_struct represents a separate domain
 * of SRCU protection.
 */
void init_srcu_struct(struct srcu_struct *sp)
{
	int i;

	sp->completed = 0;
	spin_lock_init(&sp->mutex);
	for_each_thread(i) {
		sp->per_thread(per_thread_count, i).c[0] = 0;
		sp->per_thread(per_thread_count, i).c[1] = 0;
	}
}

/*
 * srcu_readers_active_idx -- returns approximate number of readers
 *	active on the specified rank of per-CPU counters.
 */

static int srcu_readers_active_idx(struct srcu_struct *sp, int idx)
{
	int cpu;
	int sum;

	sum = 0;
	for_each_possible_cpu(cpu)
		sum += sp->per_thread(per_thread_count, cpu).c[idx];
	return sum;
}

/**
 * srcu_readers_active - returns approximate number of readers.
 * @sp: which srcu_struct to count active readers (holding srcu_read_lock).
 *
 * Note that this is not an atomic primitive, and can therefore suffer
 * severe errors when invoked on an active srcu_struct.  That said, it
 * can be useful as an error check at cleanup time.
 */
static int srcu_readers_active(struct srcu_struct *sp)
{
	return srcu_readers_active_idx(sp, 0) + srcu_readers_active_idx(sp, 1);
}

/**
 * cleanup_srcu_struct - deconstruct a sleep-RCU structure
 * @sp: structure to clean up.
 *
 * Must invoke this after you are finished using a given srcu_struct that
 * was initialized via init_srcu_struct(), else you leak memory.
 */
void cleanup_srcu_struct(struct srcu_struct *sp)
{
	int sum;

	sum = srcu_readers_active(sp);
	if (sum != 0)
		return;
}

/*
 * Counts the new reader in the appropriate per-CPU element of the
 * srcu_struct.  Must be called from process context.
 * Returns an index that must be passed to the matching srcu_read_unlock().
 */
int __srcu_read_lock(struct srcu_struct *sp)
{
	int idx;

	rcu_read_lock();
	idx = sp->completed & 0x1;
	barrier();  /* ensure compiler looks -once- at sp->completed. */
	sp->per_thread(per_thread_count, smp_processor_id()).c[idx]++;
	barrier();  /* ensure compiler won't misorder critical section. */
	rcu_read_unlock();
	return idx;
}

/*
 * Removes the count for the old reader from the appropriate per-CPU
 * element of the srcu_struct.  Note that this may well be a different
 * CPU than that which was incremented by the corresponding srcu_read_lock().
 * Must be called from process context.
 */
void __srcu_read_unlock(struct srcu_struct *sp, int idx)
{
	rcu_read_lock();
	barrier();  /* ensure compiler won't misorder critical section. */
	sp->per_thread(per_thread_count, smp_processor_id()).c[idx]--;
	rcu_read_unlock();
}

/*
 * We use an adaptive strategy for synchronize_srcu() and especially for
 * synchronize_srcu_expedited().  We spin for a fixed time period
 * (defined below) to allow SRCU readers to exit their read-side critical
 * sections.  If there are still some readers after 10 microseconds,
 * we repeatedly block for 1-millisecond time periods.  This approach
 * has done well in testing, so there is no need for a config parameter.
 */
#define SYNCHRONIZE_SRCU_READER_DELAY 10

/*
 * Wait for all pre-existing SRCU read-side critical sections.
 */
void synchronize_srcu(struct srcu_struct *sp)
{
	int idx;

	idx = sp->completed;
	spin_lock(&sp->mutex);

	/*
	 * Check to see if someone else did the work for us while we were
	 * waiting to acquire the lock.  We need -two- advances of
	 * the counter, not just one.  If there was but one, we might have
	 * shown up -after- our helper's first synchronize_sched(), thus
	 * having failed to prevent CPU-reordering races with concurrent
	 * srcu_read_unlock()s on other CPUs (see comment below).  So we
	 * either (1) wait for two or (2) supply the second ourselves.
	 */

	if ((sp->completed - idx) >= 2) {
		spin_unlock(&sp->mutex);
		return;
	}

	synchronize_rcu();  /* Force memory barrier on all CPUs. */

	/*
	 * The preceding synchronize_sched() ensures that any CPU that
	 * sees the new value of sp->completed will also see any preceding
	 * changes to data structures made by this CPU.  This prevents
	 * some other CPU from reordering the accesses in its SRCU
	 * read-side critical section to precede the corresponding
	 * srcu_read_lock() -- ensuring that such references will in
	 * fact be protected.
	 *
	 * So it is now safe to do the flip.
	 */

	idx = sp->completed & 0x1;
	sp->completed++;

	synchronize_rcu();  /* Force memory barrier on all CPUs. */

	/*
	 * At this point, because of the preceding synchronize_sched(),
	 * all srcu_read_lock() calls using the old counters have completed.
	 * Their corresponding critical sections might well be still
	 * executing, but the srcu_read_lock() primitives themselves
	 * will have finished executing.  We initially give readers
	 * an arbitrarily chosen 10 microseconds to get out of their
	 * SRCU read-side critical sections, then loop waiting 1/HZ
	 * seconds per iteration.  The 10-microsecond value has done
	 * very well in testing.
	 */

	/* if (srcu_readers_active_idx(sp, idx))
		udelay(SYNCHRONIZE_SRCU_READER_DELAY); */
	while (srcu_readers_active_idx(sp, idx))
		poll(NULL, 0, 10);

	synchronize_rcu();  /* Force memory barrier on all CPUs. */

	/*
	 * The preceding synchronize_rcu() forces all srcu_read_unlock()
	 * primitives that were executing concurrently with the preceding
	 * for_each_possible_cpu() loop to have completed by this point.
	 * More importantly, it also forces the corresponding SRCU read-side
	 * critical sections to have also completed, and the corresponding
	 * references to SRCU-protected data items to be dropped.
	 *
	 * Note:
	 *
	 *	Despite what you might think at first glance, the
	 *	preceding synchronize_rcu() -must- be within the
	 *	critical section ended by the following spin_unlock().
	 *	Otherwise, a task taking the early exit can race
	 *	with a srcu_read_unlock(), which might have executed
	 *	just before the preceding srcu_readers_active() check,
	 *	and whose CPU might have reordered the srcu_read_unlock()
	 *	with the preceding critical section.  In this case, there
	 *	is nothing preventing the synchronize_rcu() task that is
	 *	taking the early exit from freeing a data structure that
	 *	is still being referenced (out of order) by the task
	 *	doing the srcu_read_unlock().
	 *
	 *	Alternatively, the comparison with "2" on the early exit
	 *	could be changed to "3", but this increases synchronize_srcu()
	 *	latency for bulk loads.  So the current code is preferred.
	 */

	spin_unlock(&sp->mutex);
}

/**
 * srcu_batches_completed - return batches completed.
 * @sp: srcu_struct on which to report batch completion.
 *
 * Report the number of batches, correlated with, but not necessarily
 * precisely the same as, the number of grace periods that have elapsed.
 */

long srcu_batches_completed(struct srcu_struct *sp)
{
	return sp->completed;
}
