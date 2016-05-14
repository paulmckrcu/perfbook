/*
 * skiplist_glock.c: Simple RCU-protected concurrent skiplists with
 *	updates protected by single global lock.  This global lock
 *	is the skiplist head node's ->sl_lock.
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
 * Copyright (c) 2016 Paul E. McKenney, IBM Corporation.
 */

#include "skiplist.h"

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
 * Unsynchronized lookup helper.  Returns a pointer to the node preceding
 * either the specified node (if present) or the place it would be inserted
 * (if not).  Because this is unsynchronized, the returned pointer could
 * be out of date immediately upon return.  This function cannot return NULL,
 * in the worst case, it will return a pointer to the header.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
static struct skiplist *
skiplist_lookup_help(struct skiplist *head_slp, void *key,
		     int (*cmp)(struct skiplist *slp, void *key))
{
	int level;
	struct skiplist *slp = head_slp;
	struct skiplist *next_slp;

	for (level = slp->sl_toplevel; level >= 0; level--) {
		next_slp = rcu_dereference(slp->sl_next[level]);
		while (next_slp && cmp(next_slp, key) < 0) {
			slp = next_slp;
			next_slp = rcu_dereference(slp->sl_next[level]);
		}
	}
	return slp;
}

/*
 * Unsynchronized unordered lookup.  Returns a pointer to the specified node,
 * or NULL if that node was not found.  Note that the node might be deleted
 * immediately upon return.
 *
 * The caller must be in an RCU read-side critical section, or must hold
 * the update-side lock.
 */
struct skiplist *
skiplist_lookup_relaxed(struct skiplist *head_slp, void *key,
			int (*cmp)(struct skiplist *slp, void *key))
{
	int result;
	struct skiplist *slp = skiplist_lookup_help(head_slp, key, cmp);

	while (slp && (result = cmp(slp, key)) < 0)
		slp = slp->sl_next[0];
	if (slp != head_slp && slp && !slp->sl_deleted && result == 0)
		return slp;
	return NULL;
}

static struct skiplist *
skiplist_lookup_lock_prev(struct skiplist *head_slp, void *key,
			  int (*cmp)(struct skiplist *slp, void *key),
			  struct skiplist **slpp_prev, int *result)
{
	struct skiplist *slp;
	struct skiplist *slp_prev;

	skiplist_lock(head_slp);
	slp_prev = skiplist_lookup_help(head_slp, key, cmp);
	*slpp_prev = slp_prev;
	slp = slp_prev->sl_next[0];
	if (slp && !slp->sl_deleted && (*result = cmp(slp, key)) == 0)
		return slp;
	skiplist_unlock(head_slp);
	return NULL;
}

struct skiplist *
skiplist_lookup_lock(struct skiplist *head_slp, void *key,
		     int (*cmp)(struct skiplist *slp, void *key))
{
	int result;
	struct skiplist *slp_cur;
	struct skiplist *slp_prev;

	slp_cur = skiplist_lookup_lock_prev(head_slp, key, cmp,
					    &slp_prev, &result);
	if (!slp_cur || result) {
		if (slp_cur)
			skiplist_unlock(head_slp);
		return NULL;
	}
	return slp_cur;
}

struct skiplist *skiplist_delete(struct skiplist *head_slp, void *key,
				 int (*cmp)(struct skiplist *slp, void *key))
{
	int level;
	int result;
	struct skiplist *slp;
	struct skiplist *slp_next;
	struct skiplist *update[SL_MAX_LEVELS];

	skiplist_lock(head_slp);
	slp = head_slp;
	for (level = slp->sl_toplevel; level >= 0; level--) {
		slp_next = slp->sl_next[level];
		while (slp_next && (result = cmp(slp_next, key)) < 0) {
			slp = slp_next;
			slp_next = slp->sl_next[level];
		}
		if (result)
			update[level] = NULL;
		else
			update[level] = slp;
	}
	slp = slp->sl_next[0];
	if (!slp || cmp(slp, key) != 0) {
		skiplist_unlock(head_slp);
		return NULL;
	}
	for (level = slp->sl_toplevel; level >= 0; level--)
		if (update[level])
			rcu_assign_pointer(update[level]->sl_next[level],
					   slp->sl_next[level]);
	slp->sl_deleted = 1;
	if (debug)
		skiplist_fsck(head_slp, cmp);
	skiplist_unlock(head_slp);
	return slp;
}

/*
 * Stub for skiplisttorture.
 */
static int skiplist_insert_lock(struct skiplist *head_slp, void *key,
				int (*cmp)(struct skiplist *slp, void *key),
				struct skiplist **update)
{
	return -1;
}

int skiplist_insert(struct skiplist *new_slp, struct skiplist *head_slp,
		    void *key, int (*cmp)(struct skiplist *slp, void *key))
{
	int level;
	int result;
	int toplevel = random_level();
	struct skiplist *slp;
	struct skiplist *slp_next;
	struct skiplist *update[SL_MAX_LEVELS];

	skiplist_lock(head_slp);
	slp = head_slp;
	for (level = slp->sl_toplevel; level >= 0; level--) {
		slp_next = slp->sl_next[level];
		while (slp_next && (result = cmp(slp_next, key)) < 0) {
			slp = slp_next;
			slp_next = slp->sl_next[level];
		}
		if (level > toplevel)
			update[level] = NULL;
		else
			update[level] = slp;
	}
	slp = slp->sl_next[0];
	if (slp && cmp(slp, key) == 0) {
		skiplist_unlock(head_slp);
		return -EEXIST;
	}
	new_slp->sl_toplevel = toplevel;
	spin_lock_init(&new_slp->sl_lock);
	new_slp->sl_deleted = 0;
	new_slp->sl_head = head_slp;
	for (level = 0; level <= toplevel; level++) {
		new_slp->sl_next[level] = update[level]->sl_next[level];
		BUG_ON(update[level]->sl_toplevel < level);
		smp_store_release(&update[level]->sl_next[level], new_slp);
	}
	for (; level < SL_MAX_LEVELS; level++)
		new_slp->sl_next[level] = NULL;
	if (debug)
		skiplist_fsck(head_slp, cmp);
	skiplist_unlock(head_slp);
	return 0;
}

void defer_del_rcu(struct rcu_head *rhp);

#define defer_del(p)	call_rcu(p, defer_del_rcu)

#define quiescent_state() rcu_quiescent_state()

#include "skiplisttorture.h"
