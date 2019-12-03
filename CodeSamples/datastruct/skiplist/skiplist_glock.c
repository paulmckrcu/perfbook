/*
 * skiplist_glock.c: Simple RCU-protected concurrent skiplists with
 *	updates protected by single global lock.  This global lock
 *	is the skiplist head element's ->sl_lock.
 *
 * Usage:
 *
 *	./skiplist_glock --smoketest
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

#include "skiplist.h"

/*
 * Lock the skiplist that the specified element is a member of.
 */
static void skiplist_lock(struct skiplist *slp)
{
	spin_lock(&slp->sl_head->sl_lock);
}

/*
 * Unlock the skiplist that the specified element is a member of.
 */
static void skiplist_unlock(struct skiplist *slp)
{
	spin_unlock(&slp->sl_head->sl_lock);
}

/*
 * Unlock the skiplist if the update vector indicates that it was locked.
 */
static void skiplist_unlock_update(struct skiplist **update, int toplevel)
{
	int level;

	for (level = 0; level <= toplevel; level++) {
		if (update[level]) {
			skiplist_unlock(update[level]);
			return;
		}
	}
}

/*
 * Unsynchronized lookup helper.  Returns a pointer to the element preceding
 * either the specified element (if present) or the place it would be inserted
 * (if not).  Because this is unsynchronized, the returned pointer could
 * be out of date immediately upon return.  This function cannot return NULL,
 * in the worst case, it will return a pointer to the header.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
static struct skiplist *
skiplist_lookup_help(struct skiplist *head_slp, void *key)
{
	int level;
	struct skiplist *slp = head_slp;
	struct skiplist *next_slp;

	for (level = slp->sl_toplevel; level >= 0; level--) {
		next_slp = rcu_dereference(slp->sl_next[level]);
		while (next_slp && head_slp->sl_cmp(next_slp, key) < 0) {
			slp = next_slp;
			next_slp = rcu_dereference(slp->sl_next[level]);
		}
	}
	return slp;
}

/*
 * Unsynchronized unordered lookup.  Returns a pointer to the specified element,
 * or NULL if that element was not found.  Note that the element might be
 * deleted immediately upon return.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
struct skiplist *
skiplist_lookup_relaxed(struct skiplist *head_slp, void *key)
{
	int result;
	struct skiplist *slp = skiplist_lookup_help(head_slp, key);

	while (slp && (result = head_slp->sl_cmp(slp, key)) < 0)
		slp = slp->sl_next[0];
	if (slp != head_slp && slp && !slp->sl_deleted && result == 0)
		return slp;
	return NULL;
}

/*
 * Return a pointer to the specified element if it exists, and also
 * lock the skiplist.  A pointer to the predecessor is passed back
 * through slpp_prev, and the comparison result is passed back through
 * result.  If there is no such element, return NULL, pass the
 * would-be predecessor back through slpp_prev (unlocked!), and
 * pass back a greater-than value (1) through result.  Again, if the
 * return value is NULL, the skiplist is unlocked.
 *
 * The caller must be in an RCU read-side critical section.  Do -not-
 * call this function with the skiplist locked unless you want deadlock.
 */
static struct skiplist *
skiplist_lookup_lock_prev(struct skiplist *head_slp, void *key,
			  struct skiplist **slpp_prev, int *result)
{
	struct skiplist *slp;
	struct skiplist *slp_prev;

	skiplist_lock(head_slp);
	slp_prev = skiplist_lookup_help(head_slp, key);
	*slpp_prev = slp_prev;
	slp = slp_prev->sl_next[0];
	if (slp && !slp->sl_deleted &&
	    (*result = head_slp->sl_cmp(slp, key)) == 0)
		return slp;
	*result = 1;
	skiplist_unlock(head_slp);
	return NULL;
}

/*
 * Return a pointer to the specified element if it exists, and lock
 * the skiplist.  If there is no such element, return NULL and leave
 * the skiplist unlocked.
 *
 * The caller must be in an RCU read-side critical section.  Do -not-
 * call this function with the skiplist locked unless you want deadlock.
 */
struct skiplist *
skiplist_lookup_lock(struct skiplist *head_slp, void *key)
{
	int result;
	struct skiplist *slp_cur;
	struct skiplist *slp_prev;

	slp_cur = skiplist_lookup_lock_prev(head_slp, key, &slp_prev, &result);
	if (!slp_cur || result) {
		if (slp_cur)
			skiplist_unlock(head_slp);
		return NULL;
	}
	return slp_cur;
}

/*
 * Return a pointer to the first element in the list and initialize the
 * skiplist iteration-hint structure passed in via slip, or return NULL
 * if the list is empty.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
struct skiplist *skiplist_ptriter_first(struct skiplist *head_slp,
					struct skiplist_iter *slip)
{
	slip->iter_seq = skiplist_start_reader(head_slp);
	slip->hintp = head_slp->sl_next[0];
	return slip->hintp;
}

/*
 * Return a pointer to the last element in the list and initialize the
 * skiplist iteration-hint structure passed in via slip, or return NULL
 * if the list is empty.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
struct skiplist *skiplist_ptriter_last(struct skiplist *head_slp,
				       struct skiplist_iter *slip)
{
	slip->iter_seq = skiplist_start_reader(head_slp);
	slip->hintp = skiplist_valiter_last(head_slp);
	return slip->hintp;
}

/*
 * If still valid, use the hint to find the next element.  Otherwise,
 * fall back to a key lookup.
 */
struct skiplist *
skiplist_ptriter_next(struct skiplist *head_slp, void *key,
		      struct skiplist_iter *slip)
{
	struct skiplist *slp;

	if (skiplist_retry_reader(head_slp, slip->iter_seq))
		goto regen_iter;
	slp = rcu_dereference(slip->hintp);
	if (slp == NULL)
		return NULL;
	if (ACCESS_ONCE(slp->sl_deleted))
		goto regen_iter;
	slp = rcu_dereference(slp->sl_next[0]);
	if (slp == NULL) {
		slip->hintp = NULL;
		return NULL;
	}
	if (ACCESS_ONCE(slp->sl_deleted))
		goto regen_iter;
	slip->hintp = slp;
	if (!skiplist_retry_reader(head_slp, slip->iter_seq))
		return slp;

regen_iter:
	slip->iter_seq = skiplist_start_reader(head_slp);
	slip->hintp = skiplist_valiter_next(head_slp, key);
	return slip->hintp;
}

/*
 * Find the previous element.  We don't have backwards pointers, so we
 * cannot really use the hint in this case, but we do regenerate the
 * hint in case the caller laster wants to move forwards.
 */
struct skiplist *
skiplist_ptriter_prev(struct skiplist *head_slp, void *key,
		      struct skiplist_iter *slip)
{
	slip->iter_seq = skiplist_start_reader(head_slp);
	slip->hintp = skiplist_valiter_prev(head_slp, key);
	return slip->hintp;
}

/*
 * Remove the specified element from the skiplist and return a pointer
 * to it.  The caller is responsible for disposing of the element, but
 * must ensure that a grace period elapses before doing so.  If there is
 * no such element, returns NULL.
 */
struct skiplist *skiplist_delete(struct skiplist *head_slp, void *key)
{
	int level;
	int result = 0; /* Suppress compiler warning. */
	struct skiplist *slp;
	struct skiplist *slp_next;
	struct skiplist *update[SL_MAX_LEVELS];

	skiplist_lock(head_slp);
	skiplist_start_writer(head_slp);

	/* Find all the predecessors. */
	slp = head_slp;
	for (level = slp->sl_toplevel; level >= 0; level--) {
		slp_next = slp->sl_next[level];
		while (slp_next &&
		       (result = head_slp->sl_cmp(slp_next, key)) < 0) {
			slp = slp_next;
			slp_next = slp->sl_next[level];
		}
		if (result)
			update[level] = NULL;
		else
			update[level] = slp;
	}

	/* Locate the element to be deleted, and check its identity. */
	slp = slp->sl_next[0];
	if (!slp || head_slp->sl_cmp(slp, key) != 0) {

		/* No element or wrong element. */
		skiplist_end_writer(head_slp);
		skiplist_unlock(head_slp);
		return NULL;
	}

	/* Unlink from skiplist. */
	for (level = slp->sl_toplevel; level >= 0; level--)
		if (update[level])
			rcu_assign_pointer(update[level]->sl_next[level],
					   slp->sl_next[level]);
		else
			BUG_ON(level < slp->sl_toplevel && update[level + 1]);

	/* Mark deleted and check skiplist if debugging enabled. */
	BUG_ON(slp->sl_deleted);
	slp->sl_deleted = 1;
	if (debug)
		skiplist_fsck(head_slp);

	skiplist_end_writer(head_slp);
	skiplist_unlock(head_slp);
	return slp;
}

/*
 * Stub for skiplisttorture.
 */
static int skiplist_insert_lock(struct skiplist *head_slp, void *key,
				struct skiplist **update)
{
	return -1;
}

/*
 * Insert the specified element, returning zero if successful.  Return
 * -EEXIST if element with the specified key is already in the list.
 */
int skiplist_insert(struct skiplist *new_slp, struct skiplist *head_slp,
		    void *key)
{
	int level;
	int result;
	int toplevel = random_level();
	struct skiplist *slp;
	struct skiplist *slp_next;
	struct skiplist *update[SL_MAX_LEVELS];

	skiplist_lock(head_slp);

	/* Locate predecessors for position in list. */
	slp = head_slp;
	for (level = slp->sl_toplevel; level >= 0; level--) {
		slp_next = slp->sl_next[level];
		while (slp_next &&
		       (result = head_slp->sl_cmp(slp_next, key)) < 0) {
			slp = slp_next;
			slp_next = slp->sl_next[level];
		}
		if (level > toplevel)
			update[level] = NULL;
		else
			update[level] = slp;
	}

	/* Check for pre-existing element with desired key. */
	slp = slp->sl_next[0];
	if (slp && head_slp->sl_cmp(slp, key) == 0) {

		/* Element exists, unlock and indicate failure. */
		skiplist_unlock(head_slp);
		return -EEXIST;
	}

	/* Initialize node to be inserted.  Caller is responsible for key. */
	new_slp->sl_toplevel = toplevel;
	spin_lock_init(&new_slp->sl_lock);
	new_slp->sl_deleted = 0;
	new_slp->sl_head = head_slp;

	/* Link the new node into the list.  Check skiplist if debug enabled. */
	for (level = toplevel + 1; level < SL_MAX_LEVELS; level++)
		new_slp->sl_next[level] = NULL;
	for (level = 0; level <= toplevel; level++) {
		new_slp->sl_next[level] = update[level]->sl_next[level];
		BUG_ON(update[level]->sl_toplevel < level);
		smp_store_release(&update[level]->sl_next[level], new_slp);
	}
	if (debug)
		skiplist_fsck(head_slp);

	skiplist_unlock(head_slp);
	return 0;
}

/*
 * Acquire any locks that might be needed to rebalance the specified node.
 * Return NULL without holding any locks if the node does not exist.
 */
static struct skiplist *skiplist_balance_node_lock(struct skiplist *head_slp,
						   void *key,
						   struct skiplist **update)
{
	int level;
	struct skiplist *slp;
	struct skiplist *slp_next;

	skiplist_lock(head_slp);
	slp = head_slp;
	for (level = slp->sl_toplevel; level >= 0; level--) {
		slp_next = slp->sl_next[level];
		while (slp_next && head_slp->sl_cmp(slp_next, key) < 0) {
			slp = slp_next;
			slp_next = slp->sl_next[level];
		}
		update[level] = slp;
	}
	slp = slp->sl_next[0];
	if (slp && head_slp->sl_cmp(slp, key) == 0)
		return slp;
	skiplist_unlock(head_slp);
	return NULL;
}

/*
 * Rebalance the specified skiplist node to the specified level.
 * Returns an error if the node does not exist, or if the node is already
 * at or below the specified level.  This function is intended to be used
 * for "sentinel" nodes that are not subject to removal or insertion
 */
int skiplist_balance_node(struct skiplist *head_slp, void *key, int newlevel)
{
	int level;
	struct skiplist *slp;
	struct skiplist *update[SL_MAX_LEVELS];

	slp = skiplist_balance_node_lock(head_slp, key, update);
	if (!slp)
		return -ENOENT;
	if (slp->sl_toplevel == newlevel) {
		skiplist_unlock(head_slp);
		return 0;
	}
	if (slp->sl_toplevel > newlevel) {
		/* Balance down. */
		for (level = newlevel; level > slp->sl_toplevel; level++)
			rcu_assign_pointer(update[level]->sl_next[level],
					   slp->sl_next[level]);
	} else {
		/* Balance up. */
		for (level = slp->sl_toplevel + 1; level <= newlevel; level++) {
			slp->sl_next[level] = update[level]->sl_next[level];
			rcu_assign_pointer(update[level]->sl_next[level], slp);
		}
	}
	slp->sl_toplevel = newlevel;
	skiplist_unlock(head_slp);
	return 0;
}

void defer_del_rcu(struct rcu_head *rhp);

#define defer_del(p)	call_rcu(p, defer_del_rcu)

#define quiescent_state() rcu_quiescent_state()

#ifdef TEST_SKIPLIST
#include "skiplisttorture.h"
#endif /* #ifdef TEST_SKIPLIST */
