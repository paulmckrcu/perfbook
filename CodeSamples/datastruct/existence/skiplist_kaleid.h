/*
 * skiplist_kaleid.h: Common definitions for kaleidoscopic skiplists.
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

#ifndef SKIPLIST_KALEID_H
#define SKIPLIST_KALEID_H

#include "procon.h"

struct skiplist_kaleid {
	struct skiplist sk_sle;
	struct skiplist *sk_slh;
	struct kaleidoscope_head sk_kh;
	struct keyvalue *sk_kv;
	struct procon_mblock pm;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

/* Producer/consumer memory pool. */
DEFINE_PROCON_MPOOL(skiplist_kaleid, pm, malloc(sizeof(struct skiplist_kaleid)))

/*
 * Trivial comparison function.
 */
int skiplist_kaleid_cmp(struct skiplist *slp, void *key)
{
	unsigned long a;
	unsigned long b;
	struct skiplist_kaleid *slkp;

	slkp = container_of(slp, struct skiplist_kaleid, sk_sle);
	a = (unsigned long)key;
	b = slkp->sk_kv->key;
	return (a != b) - 2 * (a < b);
}

/*
 * Look up the specified key in the specified skiplist, accounting
 * for existence structures.
 */
struct skiplist_kaleid *skiplist_kaleid_lookup(struct skiplist *slhp,
					       unsigned long key)
{
	struct skiplist *slp;
	struct skiplist_kaleid *slkp;

	slp = skiplist_lookup_relaxed(slhp, (void *)key);
	if (!slp)
		return NULL;
	slkp = container_of(slp, struct skiplist_kaleid, sk_sle);
	if (kaleidoscope_exists(&slkp->sk_kh))
		return slkp;
	return NULL;
}

/*
 * Add the specified skiplist_kaleid structure to the skiplist that it
 * references.  Returns -EEXIST if the key is already in the skiplist,
 * 0 otherwise.
 */
int skiplist_kaleid_add(struct kaleidoscope_head *khp)
{
	struct skiplist_kaleid *slkp;
	struct skiplist *slhp;
	unsigned long key;

	slkp = container_of(khp, struct skiplist_kaleid, sk_kh);
	slhp = slkp->sk_slh;
	key = slkp->sk_kv->key;
	if (skiplist_insert(&slkp->sk_sle, slhp, (void *)key))
		return -EEXIST;
	return 0;
}

/*
 * Remove the specified skiplist_kaleid structure from the skiplist that
 * it references.
 */
void skiplist_kaleid_remove(struct kaleidoscope_head *khp)
{
	struct skiplist_kaleid *slkp;
	struct skiplist *slhp;
	unsigned long key;

	slkp = container_of(khp, struct skiplist_kaleid, sk_kh);
	slhp = slkp->sk_slh;
	key = slkp->sk_kv->key;
	BUG_ON(!skiplist_delete(slhp, (void *)key));
}

/*
 * Free the specified skiplist_kaleid structure.
 */
void skiplist_kaleid_free(struct kaleidoscope_head *khp)
{
	struct skiplist_kaleid *slkp;
	struct keyvalue *kvp;

	slkp = container_of(khp, struct skiplist_kaleid, sk_kh);
	kvp = slkp->sk_kv;
	if (atomic_dec_and_test(&kvp->refcnt))
		keyvalue__procon_free(kvp);
	skiplist_kaleid__procon_free(slkp);
}

/*
 * Allocate and initialize a skiplist_kaleid structure as incoming,
 * which adds it to the specifried skiplist.  A NULL kvp_in
 * argument allocates a new keyvalue structure with the specified
 * key and value, otherwise, the specified kvp_in keyvalue structure
 * is used and the key and value arguments are ignored.
 *
 * Returns a pointer to the skiplist_kaleid structure if successful,
 * or NULL if an entry with the specified key was already in the
 * skiplist.
 */
struct skiplist_kaleid *
skiplist_kaleid_alloc(struct kaleidoscope_group *kgp, struct skiplist *slp,
		      struct keyvalue *kvp_in, int state, unsigned long key,
		      unsigned long value)
{
	struct skiplist_kaleid *slkp;
	struct keyvalue *kvp = kvp_in;

	slkp = skiplist_kaleid__procon_alloc();
	BUG_ON(!slkp);
	slkp->sk_slh = slp;
	if (kvp) {
		slkp->sk_kv = kvp;
		atomic_inc(&kvp->refcnt);
	} else {
		kvp = keyvalue__procon_alloc();
		BUG_ON(!kvp);
		kvp->key = key;
		kvp->value = value;
		atomic_set(&kvp->refcnt, 1);
		slkp->sk_kv = kvp;
	}
	if (kaleidoscope_head_init_state(&slkp->sk_kh, kgp, state,
					 skiplist_kaleid_add,
				         skiplist_kaleid_remove,
				         skiplist_kaleid_free)) {
		if (atomic_dec_and_test(&kvp->refcnt))
			keyvalue__procon_unalloc(kvp);
		skiplist_kaleid__procon_unalloc(slkp);
		return NULL;
	}
	return slkp;
}

#endif /* #ifndef SKIPLIST_KALEID_H */
