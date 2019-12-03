/*
 * skiplist.h: Common definitions for simple RCU-protected concurrent skiplists.
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

#define _LGPL_SOURCE
#include "../../api.h"

#include "../../lib/random.h"

// Uncomment to enable signal-based RCU.  (Need corresponding Makefile change!)
#define RCU_SIGNAL
#include <urcu.h>

// Uncomment to enable QSBR.  (Need corresponding Makefile change!)
//#include <urcu-qsbr.h>

#define SL_MAX_LEVELS 8

/*
 * Skiplist element.
 */
struct skiplist {
	int sl_toplevel;
	spinlock_t sl_lock;
	int sl_deleted;
	struct skiplist *sl_head;
	unsigned long sl_seq;
	int (*sl_cmp)(struct skiplist *slp, void *key);
	struct skiplist *sl_next[SL_MAX_LEVELS];
};

/*
 * Skiplist iterator hint structure.  Opaque outside of skiplist
 * implementation.
 */
struct skiplist_iter {
	struct skiplist *hintp;
	unsigned long iter_seq;
};

struct skiplist *skiplist_ptriter_first(struct skiplist *head_slp,
					struct skiplist_iter *slip);
struct skiplist *skiplist_ptriter_last(struct skiplist *head_slp,
				       struct skiplist_iter *slip);
struct skiplist *
skiplist_ptriter_next(struct skiplist *head_slp, void *key,
		      struct skiplist_iter *slip);
struct skiplist *
skiplist_ptriter_prev(struct skiplist *head_slp, void *key,
		      struct skiplist_iter *slip);

int skiplist_balance_node(struct skiplist *head_slp, void *key, int newlevel);

static struct skiplist *
skiplist_lookup_help(struct skiplist *head_slp, void *key);

static int __attribute__((unused)) debug;

/*
 * Initialize a skiplist header.
 */
void skiplist_init(struct skiplist *slp,
		   int (*cmp)(struct skiplist *slp, void *key))
{
	int i;

	slp->sl_toplevel = SL_MAX_LEVELS - 1;
	spin_lock_init(&slp->sl_lock);
	slp->sl_deleted = 0;
	slp->sl_head = slp;
	slp->sl_seq = 0;
	slp->sl_cmp = cmp;
	for (i = 0; i < SL_MAX_LEVELS; i++)
		slp->sl_next[i] = NULL;
}

/*
 * Pick up a read-side sequence number, which can later be checked against
 * a new sequence number to detect intervening updates.
 *
 * The caller must in in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
static unsigned long __attribute__((unused))
skiplist_start_reader(struct skiplist *head_slp)
{
	unsigned long ret;

	ret = ACCESS_ONCE(head_slp->sl_seq) & ~0x1;
	smp_mb();
	return ret;
}

/*
 * Check a read-side sequence number, returning 1 to indicate a need to
 * retry the reader.
 *
 * The caller must in in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
static unsigned long __attribute__((unused))
skiplist_retry_reader(struct skiplist *head_slp, unsigned long seq)
{
	smp_mb();
	return ACCESS_ONCE(head_slp->sl_seq) != seq;
}

/*
 * Update sequence number to reflect starting a writer.  Note that this
 * function assumes that there is only one writer, for example, the
 * skiplist lock must be held.
 */
static void __attribute__((unused))
skiplist_start_writer(struct skiplist *head_slp)
{
	ACCESS_ONCE(head_slp->sl_seq) = head_slp->sl_seq + 1;
	smp_mb();
	BUG_ON(!(head_slp->sl_seq & 0x1));
}

/*
 * Update sequence number to reflect ending a writer.  Note that this
 * function assumes that there is only one writer, for example, the
 * skiplist lock must be held.
 */
static void __attribute__((unused))
skiplist_end_writer(struct skiplist *head_slp)
{
	smp_mb();
	ACCESS_ONCE(head_slp->sl_seq) = head_slp->sl_seq + 1;
	BUG_ON(head_slp->sl_seq & 0x1);
}

/*
 * Pick a random level for a new element.  Exponential power-of-two decrease
 * in probability for higher levels.  Top level gets double expected
 * probability due to truncation, which is in turn due to a finite number
 * of levels.
 */
static int random_level(void)
{
	int i = 0;
	unsigned long r = random();

	while (r & 0x1) {
		i++;
		r >>= 1;
	}
	if (i >= SL_MAX_LEVELS)
		return SL_MAX_LEVELS - 1;
	return i;
}

/*
 * Return a pointer to the first element in the list, or NULL if the
 * list is empty.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
struct skiplist *skiplist_valiter_first(struct skiplist *head_slp)
{
	return head_slp->sl_next[0];
}

/*
 * Return a pointer to the last element in the list, or NULL if the
 * list is empty.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
struct skiplist *skiplist_valiter_last(struct skiplist *head_slp)
{
	int level;
	struct skiplist *slp = head_slp;
	struct skiplist *slp_next;

	for (level = head_slp->sl_toplevel; level >= 0; level--) {
		slp_next = rcu_dereference(slp->sl_next[level]);
		while (slp_next != NULL) {
			slp = slp_next;
			slp_next = rcu_dereference(slp->sl_next[level]);
		}
	}
	return slp == head_slp ? NULL : slp;
}

/*
 * Return a pointer to the first element in the list with a key larger than
 * specified, or NULL if there is no such element.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
struct skiplist *
skiplist_valiter_next(struct skiplist *head_slp, void *key)
{
	int level;
	struct skiplist *slp = head_slp;
	struct skiplist *next_slp;

	/* Find the element preceding the desired next element. */
	for (level = slp->sl_toplevel; level >= 0; level--) {
		next_slp = rcu_dereference(slp->sl_next[level]);
		while (next_slp && head_slp->sl_cmp(next_slp, key) <= 0) {
			slp = next_slp;
			next_slp = rcu_dereference(slp->sl_next[level]);
		}
	}

	/* Find the desired next element.  Insertions can happen! */
	next_slp = rcu_dereference(slp->sl_next[0]);
	while (next_slp && head_slp->sl_cmp(next_slp, key) <= 0) {
		slp = next_slp;
		next_slp = rcu_dereference(slp->sl_next[0]);
	}
	return next_slp;
}

/*
 * Return a pointer to the last element in the list with a key smaller than
 * specified, or NULL if there is no such element.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
struct skiplist *
skiplist_valiter_prev(struct skiplist *head_slp, void *key)
{
	struct skiplist *slp = skiplist_lookup_help(head_slp, key);

	return slp == head_slp ? NULL : slp;
}

/*
 * Consistency check for specified element against downstream elements.
 * Make sure lower-level list is connected to each downstream element,
 * and that the downstream element is tall enough.
 */
void skiplist_fsck_one(struct skiplist *first_slp)
{
	int i;
	struct skiplist *slp;

	slp = first_slp->sl_next[0];
	for (i = 1; i <= first_slp->sl_toplevel; i++) {
		while (slp != first_slp->sl_next[i]) {
			assert(slp);
			slp = slp->sl_next[0];
		}
		assert(!slp || slp->sl_toplevel >= i);
	}
	for (; i < SL_MAX_LEVELS; i++)
		assert(!first_slp->sl_next[i]);
}

/*
 * Consistency check specified skiplist.
 */
void skiplist_fsck(struct skiplist *head_slp)
{
	struct skiplist *slp;

	for (slp = head_slp; slp; slp = slp->sl_next[0]) {
		skiplist_fsck_one(slp);
		BUG_ON(slp->sl_head != head_slp);
	}
}
