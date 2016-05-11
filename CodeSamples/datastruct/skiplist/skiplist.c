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
 * Copyright (c) 2016 Paul E. McKenney, IBM Corporation.
 */

#define _LGPL_SOURCE
#include "../../api.h"

// Uncomment to enable signal-based RCU.  (Need corresponding Makefile change!)
#define RCU_SIGNAL
#include <urcu.h>

// Uncomment to enable QSBR.  (Need corresponding Makefile change!)
//#include <urcu-qsbr.h>

#define SL_MAX_LEVELS 8

struct skiplist {
	int sl_toplevel;
	spinlock_t sl_lock;
	int sl_deleted;
	struct skiplist *sl_next[SL_MAX_LEVELS];
};

/*
 * Initialize a skiplist header.
 */
void skiplist_init(struct skiplist *slp)
{
	int i;

	slp->sl_toplevel = SL_MAX_LEVELS - 1;
	spin_lock_init(&slp->sl_lock);
	slp->sl_deleted = 0;
	for (i = 0; i < SL_MAX_LEVELS; i++)
		slp->sl_next[i] = NULL;
}

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
			return;
		if (update[level] != slp_last) {
			slp_last = update[level];
			skiplist_unlock(slp_last);
		}
	}
}

static struct skiplist *
skiplist_lookup_help(struct skiplist *head_slp, void *key,
		     int (*cmp)(struct skiplist *slp, void *key))
{
	struct skiplist *slp = head_slp;
	int level;

	for (level = slp->sl_toplevel; level >= 0; level--) {
		while (slp->sl_next[level] && cmp(slp->sl_next[level], key) < 0)
			slp = rcu_dereference(slp->sl_next[level]);
	}
	return slp;
}

struct skiplist *
skiplist_lookup_relaxed(struct skiplist *head_slp, void *key,
			int (*cmp)(struct skiplist *slp, void *key))
{
	struct skiplist *slp = skiplist_lookup_help(head_slp, key, cmp);

	slp = slp->sl_next[0];
	if (slp && !slp->sl_deleted && cmp(slp, key) == 0)
		return slp;
	return NULL;
}

static struct skiplist *
skiplist_lookup_lock_prev(struct skiplist *head_slp, void *key,
			  int (*cmp)(struct skiplist *slp, void *key),
			  struct skiplist **slpp_prev, int *result)
{
	struct skiplist *slp_cur;
	struct skiplist *slp_prev;

	for (;;) {
		slp_prev = skiplist_lookup_help(head_slp, key, cmp);
		skiplist_lock(slp_prev);
		if (slp_prev->sl_deleted)
			goto unlock_retry;
		slp_cur = slp_prev->sl_next[0];
		*slpp_prev = slp_prev;
		if (!slp_cur) {
			*result = 1;
			return NULL;
		}
		*result = cmp(slp_cur, key);
		if (*result >= 0)
			return slp_cur;
unlock_retry:
		skiplist_unlock(slp_prev);
	}
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
		skiplist_unlock(slp_prev);
		return NULL;
	}
	skiplist_lock(slp_cur);
	skiplist_unlock(slp_prev);
	return slp_cur;
}

struct skiplist *skiplist_delete(struct skiplist *head_slp, void *key,
				 int (*cmp)(struct skiplist *slp, void *key))
{
	int level;
	int result;
	struct skiplist *slp_cur;
	struct skiplist *slp_last = NULL;
	struct skiplist *slp_prev = head_slp;
	int toplevel;
	struct skiplist *update[SL_MAX_LEVELS];

retry:
	rcu_read_lock();
	toplevel = slp_prev->sl_toplevel;
	for (level = slp_prev->sl_toplevel; level >= 0; level--) {
		slp_cur = rcu_dereference(slp_prev->sl_next[level]);
		while (slp_cur && (result = cmp(slp_cur, key)) < 0) {
			slp_prev = slp_cur;
			slp_cur = rcu_dereference(slp_prev->sl_next[level]);
		}
		if (slp_cur && result == 0) {
			if (slp_prev != slp_last) {
				skiplist_lock(slp_prev);
				slp_last = slp_prev;
			}
			update[level] = slp_prev;
		} else {
			update[level] = NULL;
		}
	}
	if (!slp_cur || result != 0) {
		skiplist_unlock_update(update, toplevel);
		rcu_read_unlock();
		return NULL;
	}
	for (level = slp_cur->sl_toplevel; level >= 0; level--) {
		if (update[level]->sl_deleted ||
		    update[level]->sl_next[level] != slp_cur) {
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
	slp_cur->sl_deleted = 1;
	skiplist_unlock_update(update, slp_cur->sl_toplevel);
	skiplist_unlock(slp_cur);
	rcu_read_unlock();
	return slp_cur;
}

static int skiplist_insert_lock(struct skiplist *head_slp, void *key,
				int (*cmp)(struct skiplist *slp, void *key),
				struct skiplist **update)
{
	int level;
	struct skiplist *slp;
	int toplevel = random_level();

retry:
	slp = head_slp;
	for (level = slp->sl_toplevel; level >= 0; level--) {
		while (slp->sl_next[level] &&
		       cmp(slp->sl_next[level], key) < 0)
			slp = slp->sl_next[level];
		if (level > toplevel) {
			update[level] = NULL;
		} else {
			update[level] = slp;
			if (level == toplevel ||
			    update[level] != update[level + 1])
				skiplist_lock(slp);
		}
	}
	for (level = 0; level <= toplevel; level++)
		if (update[level]->sl_deleted) {
			skiplist_unlock_update(update, toplevel);
			goto retry;
		}
	slp = update[0]->sl_next[0];
	if (!slp || cmp(slp, key) > 0)
		return toplevel;
	skiplist_unlock_update(update, toplevel);
	return -1;
}

int skiplist_insert(struct skiplist *new_slp, struct skiplist *head_slp,
		    void *key, int (*cmp)(struct skiplist *slp, void *key))
{
	int level;
	int toplevel;
	struct skiplist *update[SL_MAX_LEVELS];

	rcu_read_lock();
	toplevel = skiplist_insert_lock(head_slp, key, cmp, update);
	if (toplevel < 0) {
		rcu_read_unlock();
		return -EEXIST;
	}
	new_slp->sl_toplevel = toplevel;
	spin_lock_init(&new_slp->sl_lock);
	new_slp->sl_deleted = 0;
	skiplist_lock(new_slp);
	for (level = 0; level <= toplevel; level++) {
		new_slp->sl_next[level] = update[level]->sl_next[level];
		assert(update[level]->sl_toplevel >= level);
		smp_store_release(&update[level]->sl_next[level], new_slp);
	}
	for (; level < SL_MAX_LEVELS; level++)
		new_slp->sl_next[level] = NULL;
	skiplist_unlock_update(update, toplevel);
	skiplist_unlock(new_slp);
	rcu_read_unlock();
	return 0;
}

void skiplist_fsck_one(struct skiplist *first_slp,
		       int (*cmp)(struct skiplist *slp, void *key))
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

void skiplist_fsck(struct skiplist *head_slp,
		   int (*cmp)(struct skiplist *slp, void *key))
{
	struct skiplist *slp;

	for (slp = head_slp; slp; slp = slp->sl_next[0])
		skiplist_fsck_one(slp, cmp);
}

void defer_del_rcu(struct rcu_head *rhp);

#define defer_del(p)	call_rcu(p, defer_del_rcu)

#define quiescent_state() rcu_quiescent_state()

#include "skiplisttorture.h"
