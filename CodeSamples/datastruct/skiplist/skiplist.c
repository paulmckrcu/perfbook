/*
 * skiplist.c: Simple RCU-protected concurrent skiplists.
 *
 * Usage:
 *
 *	./skiplist --smoketest
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

static void skiplist_lock(struct skiplist *slp)
{
	spin_lock(&slp->sl_lock);
}

static void skiplist_unlock(struct skiplist *slp)
{
	spin_unlock(&slp->sl_lock);
}

static void skiplist_unlock_update(struct skiplist **update, int toplevel)
{
	int level;
	struct skiplist *slp_last = NULL;

	for (level = 0; level <= toplevel; level++) {
		if (!update[level])
			continue;
		if (update[level] != slp_last) {
			slp_last = update[level];
			skiplist_unlock(slp_last);
		}
	}
}

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

struct skiplist *
skiplist_lookup_relaxed(struct skiplist *head_slp, void *key)
{
	struct skiplist *slp = skiplist_lookup_help(head_slp, key);

	/* rcu_dereference() pairs with rcu_assign_pointer() in skiplist_insert*/
	slp = rcu_dereference(slp->sl_next[0]);
	if (slp != head_slp && slp && !slp->sl_deleted &&
	    head_slp->sl_cmp(slp, key) == 0)
		return slp;
	return NULL;
}

static struct skiplist *
skiplist_lookup_lock_prev(struct skiplist *head_slp, void *key,
			  struct skiplist **slpp_prev, int *result)
{
	struct skiplist *slp_cur;
	struct skiplist *slp_prev;

	for (;;) {
		slp_prev = skiplist_lookup_help(head_slp, key);
		skiplist_lock(slp_prev);
		if (slp_prev->sl_deleted)
			goto unlock_retry;
		slp_cur = slp_prev->sl_next[0];
		*slpp_prev = slp_prev;
		if (!slp_cur || slp_cur->sl_deleted) {
			skiplist_unlock(slp_prev);
			*result = 1;
			return NULL;
		}
		*result = head_slp->sl_cmp(slp_cur, key);
		if (*result >= 0)
			return slp_cur;
unlock_retry:
		skiplist_unlock(slp_prev);
	}
}

struct skiplist *
skiplist_lookup_lock(struct skiplist *head_slp, void *key)
{
	int result;
	struct skiplist *slp_cur;
	struct skiplist *slp_prev;

	slp_cur = skiplist_lookup_lock_prev(head_slp, key, &slp_prev, &result);

	if (!slp_cur || result) {
		if (slp_cur) /* if lock_prev() returns NULL, prev is unlocked.*/
			skiplist_unlock(slp_prev);
		return NULL;
	}
	skiplist_lock(slp_cur);
	skiplist_unlock(slp_prev);
	return slp_cur;
}

struct skiplist *skiplist_ptriter_first(struct skiplist *head_slp,
					struct skiplist_iter *slip)
{
	return skiplist_valiter_first(head_slp);
}

struct skiplist *skiplist_ptriter_last(struct skiplist *head_slp,
				       struct skiplist_iter *slip)
{
	return skiplist_valiter_last(head_slp);
}

struct skiplist *
skiplist_ptriter_next(struct skiplist *head_slp, void *key,
		      struct skiplist_iter *slip)
{
	return skiplist_valiter_next(head_slp, key);
}

struct skiplist *
skiplist_ptriter_prev(struct skiplist *head_slp, void *key,
		      struct skiplist_iter *slip)
{
	return skiplist_valiter_prev(head_slp, key);
}

struct skiplist *skiplist_delete(struct skiplist *head_slp, void *key)
{
	int i;
	int level;
	int result = 0; /* Suppress compiler warning. */
	struct skiplist *slp_cur;
	struct skiplist *slp_last;
	struct skiplist *slp_prev;
	int toplevel;
	struct skiplist *update[SL_MAX_LEVELS];

retry:
	rcu_read_lock();
	slp_last = NULL;
	slp_prev = head_slp;
	toplevel = slp_prev->sl_toplevel;
	assert(toplevel >= 0);
	for (level = slp_prev->sl_toplevel; level >= 0; level--) {
		slp_cur = rcu_dereference(slp_prev->sl_next[level]);
		while (slp_cur &&
		       (result = head_slp->sl_cmp(slp_cur, key)) < 0) {
			slp_prev = slp_cur;
			slp_cur = rcu_dereference(slp_prev->sl_next[level]);
		}
		if (!slp_cur || result != 0) {
			update[level] = NULL;
		} else if (slp_prev != slp_last) {
			update[level] = slp_prev;
			skiplist_lock(slp_prev);
			if (slp_cur != slp_prev->sl_next[level] ||
			    (level < slp_prev->sl_toplevel &&
			     slp_prev->sl_next[level] ==
			     slp_prev->sl_next[level + 1])) {
				/* Note: could back up to previous lock. */
				/* But if slp_last == NULL, there isn't one. */
				for (i = level - 1; i >=0; i--)
					update[i] = NULL;
				skiplist_unlock_update(update,
						       slp_cur->sl_toplevel);
				rcu_read_unlock();
				goto retry;
			}
			slp_last = slp_prev;
		} else {
			update[level] = slp_prev;
		}
	}
	if (!slp_cur || result != 0) {
		skiplist_unlock_update(update, toplevel);
		rcu_read_unlock();
		return NULL;
	}
	for (level = slp_cur->sl_toplevel; level >= 0; level--) {
		if (update[level] &&
		    (update[level]->sl_deleted ||
		     update[level]->sl_next[level] != slp_cur)) {
			skiplist_unlock_update(update, slp_cur->sl_toplevel);
			rcu_read_unlock();
			goto retry;
		}
	}
	skiplist_lock(slp_cur);
	for (level = slp_cur->sl_toplevel; level >= 0; level--)
		if (update[level])
			rcu_assign_pointer(update[level]->sl_next[level],
					   slp_cur->sl_next[level]);
	smp_store_release(&slp_cur->sl_deleted, 1);
	skiplist_unlock_update(update, slp_cur->sl_toplevel);
	skiplist_unlock(slp_cur);
	rcu_read_unlock();
	return slp_cur;
}

static int skiplist_insert_lock(struct skiplist *head_slp, void *key,
				struct skiplist **update)
{
	int i;
	int level;
	struct skiplist *slp;
	struct skiplist *slp_next;
	int toplevel = random_level();

retry:
	slp = head_slp;
	for (level = slp->sl_toplevel; level >= 0; level--) {
		slp_next = rcu_dereference(slp->sl_next[level]);
		while (slp_next && head_slp->sl_cmp(slp_next, key) < 0) {
			slp = slp_next;
			slp_next = rcu_dereference(slp->sl_next[level]);
		}
		update[level] = slp;
		if (level > toplevel) {
			update[level] = NULL;
		} else if (level == toplevel ||
			   update[level] != update[level + 1]) {
			skiplist_lock(slp);
			if (slp_next != slp->sl_next[level] ||
			    (level < slp->sl_toplevel &&
			     level < toplevel &&
			     slp->sl_next[level] == slp->sl_next[level + 1])) {
				for (i = level - 1; i >= 0; i--)
					update[i] = NULL;
				skiplist_unlock_update(update, toplevel);
				goto retry;
			}
		}
	}
	for (level = 0; level <= toplevel; level++) {
		slp = update[level];
		if (slp->sl_deleted ||
		    (slp->sl_next[level] &&
		     head_slp->sl_cmp(slp->sl_next[level], key) < 0)) {
			skiplist_unlock_update(update, toplevel);
			goto retry;
		}
	}
	slp = update[0]->sl_next[0];
	if (!slp || head_slp->sl_cmp(slp, key) > 0)
		return toplevel;
	skiplist_unlock_update(update, toplevel);
	return -1;
}

int skiplist_insert(struct skiplist *new_slp, struct skiplist *head_slp,
		    void *key)
{
	int level;
	int toplevel;
	struct skiplist *update[SL_MAX_LEVELS];

	rcu_read_lock();
	toplevel = skiplist_insert_lock(head_slp, key, update);
	if (toplevel < 0) {
		rcu_read_unlock();
		return -EEXIST;
	}
	new_slp->sl_toplevel = toplevel;
	spin_lock_init(&new_slp->sl_lock);
	new_slp->sl_deleted = 0;
	new_slp->sl_head = head_slp;
	skiplist_lock(new_slp);
	for (level = toplevel + 1; level < SL_MAX_LEVELS; level++)
		new_slp->sl_next[level] = NULL;
	for (level = 0; level <= toplevel; level++) {
		new_slp->sl_next[level] = update[level]->sl_next[level];
		assert(update[level]->sl_toplevel >= level);
		smp_store_release(&update[level]->sl_next[level], new_slp);
	}
	skiplist_unlock_update(update, toplevel);
	skiplist_unlock(new_slp);
	rcu_read_unlock();
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
	int toplevel = head_slp->sl_toplevel;

	slp = head_slp;
	for (level = toplevel; level >= 0; level--) {
		slp_next = slp->sl_next[level];
		while (slp_next && head_slp->sl_cmp(slp_next, key) < 0) {
			slp = slp_next;
			slp_next = slp->sl_next[level];
		}
		update[level] = slp;
		if (slp && (level == toplevel || slp != update[level + 1]))
			skiplist_lock(slp);
	}
	slp = slp->sl_next[0];
	if (slp && head_slp->sl_cmp(slp, key) == 0)
		return slp;
	skiplist_unlock_update(update, head_slp->sl_toplevel);
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
		skiplist_unlock_update(update, head_slp->sl_toplevel);
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
	skiplist_unlock_update(update, head_slp->sl_toplevel);
	return 0;
}

void defer_del_rcu(struct rcu_head *rhp);

#ifdef TEST_SKIPLIST
#define defer_del(p)	call_rcu(p, defer_del_rcu)

#define quiescent_state() rcu_quiescent_state()

#include "skiplisttorture.h"
#endif /* #ifdef TEST_SKIPLIST */
