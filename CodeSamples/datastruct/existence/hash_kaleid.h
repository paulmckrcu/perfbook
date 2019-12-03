/*
 * hash_kaleid.h: Common definitions for kaleidoscopic hash tables.
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

#ifndef HASH_KALEID_H
#define HASH_KALEID_H

#include "procon.h"

struct hash_kaleid {
	struct ht_elem hk_hte;
	struct hashtab *hk_htp;
	struct kaleidoscope_head hk_kh;
	struct keyvalue *hk_kv;
	struct procon_mblock pm;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

/* Producer/consumer memory pool. */
DEFINE_PROCON_MPOOL(hash_kaleid, pm, malloc(sizeof(struct hash_kaleid)))

/*
 * Trivial comparison function.
 */
int hash_kaleid_cmp(struct ht_elem *htep, void *key)
{
	struct hash_kaleid *hkp;

	hkp = container_of(htep, struct hash_kaleid, hk_hte);
	return ((unsigned long)key) == hkp->hk_kv->key;
}

/*
 * Look up the specified key in the specified hash table, accounting
 * for kaleidoscopic structures.
 */
struct hash_kaleid *hash_kaleid_lookup(struct hashtab *htp, unsigned long key)
{
	struct ht_elem *htep;
	struct hash_kaleid *hkp;

	htep = hashtab_lookup(htp, key, (void *)key);
	if (!htep)
		return NULL;
	hkp = container_of(htep, struct hash_kaleid, hk_hte);
	if (kaleidoscope_exists(&hkp->hk_kh))
		return hkp;
	return NULL;
}

/*
 * Add the specified hash_kaleid structure to the hash table that it
 * references.  Returns -EEXIST if the key is already in the hash
 * table, 0 otherwise.
 */
int hash_kaleid_add(struct kaleidoscope_head *khp)
{
	struct hash_kaleid *hkp;
	struct hashtab *htp;
	unsigned long key;

	hkp = container_of(khp, struct hash_kaleid, hk_kh);
	htp = hkp->hk_htp;
	key = hkp->hk_kv->key;
	hashtab_lock_mod(htp, key);
	if (hashtab_lookup(htp, key, (void *)key)) {
		hashtab_unlock_mod(htp, key);
		return -EEXIST;
	}
	hashtab_add(htp, key, &hkp->hk_hte);
	hashtab_unlock_mod(htp, key);
	return 0;
}

/*
 * Remove the specified hash_kaleid structure from the hash table that
 * it references.
 */
void hash_kaleid_remove(struct kaleidoscope_head *khp)
{
	struct hash_kaleid *hkp;
	struct hashtab *htp;
	unsigned long key;

	hkp = container_of(khp, struct hash_kaleid, hk_kh);
	htp = hkp->hk_htp;
	key = hkp->hk_kv->key;
	hashtab_lock_mod(htp, key);
	hashtab_del(&hkp->hk_hte);
	hashtab_unlock_mod(htp, key);
}

/*
 * Free the specified hash_kaleid structure.
 */
void hash_kaleid_free(struct kaleidoscope_head *khp)
{
	struct hash_kaleid *hkp;
	struct keyvalue *kvp;

	hkp = container_of(khp, struct hash_kaleid, hk_kh);
	kvp = hkp->hk_kv;
	if (atomic_dec_and_test(&kvp->refcnt))
		keyvalue__procon_free(kvp);
	hash_kaleid__procon_free(hkp);
}

/*
 * Allocate and initialize a hash_kaleid structure as incoming,
 * which adds it to the specifried hash table.  A NULL kvp_in
 * argument allocates a new keyvalue structure with the specified
 * key and value, otherwise, the specified kvp_in keyvalue structure
 * is used and the key and value arguments are ignored.
 *
 * Returns a pointer to the hash_kaleid structure if successful,
 * or NULL if an entry with the specified key was already in the
 * hash table.
 */
struct hash_kaleid *
hash_kaleid_alloc(struct kaleidoscope_group *kgp, struct hashtab *htp,
		  struct keyvalue *kvp_in, int state, unsigned long key,
		  unsigned long value)
{
	struct hash_kaleid *hkp;
	struct keyvalue *kvp = kvp_in;

	hkp = hash_kaleid__procon_alloc();
	BUG_ON(!hkp);
	hkp->hk_htp = htp;
	if (kvp) {
		hkp->hk_kv = kvp;
		atomic_inc(&kvp->refcnt);
	} else {
		kvp = keyvalue__procon_alloc();
		BUG_ON(!kvp);
		kvp->key = key;
		kvp->value = value;
		atomic_set(&kvp->refcnt, 1);
		hkp->hk_kv = kvp;
	}
	if (kaleidoscope_head_init_state(&hkp->hk_kh, kgp, state,
					 hash_kaleid_add, hash_kaleid_remove,
				         hash_kaleid_free)) {
		if (atomic_dec_and_test(&kvp->refcnt))
			keyvalue__procon_unalloc(kvp);
		hash_kaleid__procon_unalloc(hkp);
		return NULL;
	}
	return hkp;
}

#endif /* #ifndef HASH_KALEID_H */
