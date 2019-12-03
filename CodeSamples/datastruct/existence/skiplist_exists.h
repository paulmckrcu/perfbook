/*
 * skiplist_exists.h: Common definitions for existence-based skiplists.
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

#ifndef SKIPLIST_EXISTS_H
#define SKIPLIST_EXISTS_H

#include "procon.h"

struct skiplist_exists {
	struct skiplist se_sle;
	struct skiplist *se_slh;
	struct existence_head se_eh;
	struct keyvalue *se_kv;
	struct procon_mblock pm;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

/* Producer/consumer memory pool. */
DEFINE_PROCON_MPOOL(skiplist_exists, pm, malloc(sizeof(struct skiplist_exists)))

/*
 * Trivial comparison function.
 */
int skiplist_exists_cmp(struct skiplist *slp, void *key)
{
	unsigned long a;
	unsigned long b;
	struct skiplist_exists *slep;

	slep = container_of(slp, struct skiplist_exists, se_sle);
	a = (unsigned long)key;
	b = slep->se_kv->key;
	return (a != b) - 2 * (a < b);
}

/*
 * Look up the specified key in the specified skiplist, accounting
 * for existence structures.
 */
struct skiplist_exists *skiplist_exists_lookup(struct skiplist *slhp,
					       unsigned long key)
{
	struct skiplist *slp;
	struct skiplist_exists *slep;

	slp = skiplist_lookup_relaxed(slhp, (void *)key);
	if (!slp)
		return NULL;
	slep = container_of(slp, struct skiplist_exists, se_sle);
	if (existence_exists(&slep->se_eh))
		return slep;
	return NULL;
}

/*
 * Add the specified skiplist_exists structure to the skiplist that it
 * references.  Returns -EEXIST if the key is already in the skiplist,
 * 0 otherwise.
 */
int skiplist_exists_add(struct existence_head *ehp)
{
	struct skiplist_exists *slep;
	struct skiplist *slhp;
	unsigned long key;

	slep = container_of(ehp, struct skiplist_exists, se_eh);
	slhp = slep->se_slh;
	key = slep->se_kv->key;
	if (skiplist_insert(&slep->se_sle, slhp, (void *)key))
		return -EEXIST;
	return 0;
}

/*
 * Remove the specified skiplist_exists structure from the skiplist that
 * it references.
 */
void skiplist_exists_remove(struct existence_head *ehp)
{
	struct skiplist_exists *slep;
	struct skiplist *slhp;
	unsigned long key;

	slep = container_of(ehp, struct skiplist_exists, se_eh);
	slhp = slep->se_slh;
	key = slep->se_kv->key;
	BUG_ON(!skiplist_delete(slhp, (void *)key));
}

/*
 * Free the specified skiplist_exists structure.
 */
void skiplist_exists_free(struct existence_head *ehp)
{
	struct skiplist_exists *slep;
	struct keyvalue *kvp;

	slep = container_of(ehp, struct skiplist_exists, se_eh);
	kvp = slep->se_kv;
	if (atomic_dec_and_test(&kvp->refcnt))
		keyvalue__procon_free(kvp);
	skiplist_exists__procon_free(slep);
}

/*
 * Allocate and initialize a skiplist_exists structure as incoming,
 * which adds it to the specifried skiplist.  A NULL kvp_in
 * argument allocates a new keyvalue structure with the specified
 * key and value, otherwise, the specified kvp_in keyvalue structure
 * is used and the key and value arguments are ignored.
 *
 * Returns a pointer to the skiplist_exists structure if successful,
 * or NULL if an entry with the specified key was already in the
 * skiplist.
 */
struct skiplist_exists *
skiplist_exists_alloc(struct existence_group *egp, struct skiplist *slp,
		     struct keyvalue *kvp_in, unsigned long key,
		     unsigned long value)
{
	struct skiplist_exists *slep;
	struct keyvalue *kvp = kvp_in;

	slep = skiplist_exists__procon_alloc();
	BUG_ON(!slep);
	slep->se_slh = slp;
	if (kvp) {
		slep->se_kv = kvp;
		atomic_inc(&kvp->refcnt);
	} else {
		kvp = keyvalue__procon_alloc();
		BUG_ON(!kvp);
		kvp->key = key;
		kvp->value = value;
		atomic_set(&kvp->refcnt, 1);
		slep->se_kv = kvp;
	}
	if (existence_head_init_incoming(&slep->se_eh, egp, skiplist_exists_add,
				         skiplist_exists_remove,
				         skiplist_exists_free)) {
		if (atomic_dec_and_test(&kvp->refcnt))
			keyvalue__procon_unalloc(kvp);
		skiplist_exists__procon_unalloc(slep);
		return NULL;
	}
	return slep;
}

#endif /* #ifndef SKIPLIST_EXISTS_H */
