/*
 * hash_exists.h: Common definitions for existence-based hash tables.
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

#ifndef HASH_EXISTS_H
#define HASH_EXISTS_H

#include "procon.h"

struct hash_exists {
	struct ht_elem he_hte;
	struct hashtab *he_htp;
	struct existence_head he_eh;
	struct keyvalue *he_kv;
	struct procon_mblock pm;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

/* Producer/consumer memory pool. */
DEFINE_PROCON_MPOOL(hash_exists, pm, malloc(sizeof(struct hash_exists)))

/*
 * Trivial comparison function.
 */
int hash_exists_cmp(struct ht_elem *htep, void *key)
{
	struct hash_exists *hep;

	hep = container_of(htep, struct hash_exists, he_hte);
	return ((unsigned long)key) == hep->he_kv->key;
}

/*
 * Look up the specified key in the specified hash table, accounting
 * for existence structures.
 */
struct hash_exists *hash_exists_lookup(struct hashtab *htp, unsigned long key)
{
	struct ht_elem *htep;
	struct hash_exists *hep;

	htep = hashtab_lookup(htp, key, (void *)key);
	if (!htep)
		return NULL;
	hep = container_of(htep, struct hash_exists, he_hte);
	if (existence_exists(&hep->he_eh))
		return hep;
	return NULL;
}

/*
 * Add the specified hash_exists structure to the hash table that it
 * references.  Returns -EEXIST if the key is already in the hash
 * table, 0 otherwise.
 */
int hash_exists_add(struct existence_head *ehp)
{
	struct hash_exists *hep;
	struct hashtab *htp;
	unsigned long key;

	hep = container_of(ehp, struct hash_exists, he_eh);
	htp = hep->he_htp;
	key = hep->he_kv->key;
	hashtab_lock_mod(htp, key);
	if (hashtab_lookup(htp, key, (void *)key)) {
		hashtab_unlock_mod(htp, key);
		return -EEXIST;
	}
	hashtab_add(htp, key, &hep->he_hte);
	hashtab_unlock_mod(htp, key);
	return 0;
}

/*
 * Remove the specified hash_exists structure from the hash table that
 * it references.
 */
void hash_exists_remove(struct existence_head *ehp)
{
	struct hash_exists *hep;
	struct hashtab *htp;
	unsigned long key;

	hep = container_of(ehp, struct hash_exists, he_eh);
	htp = hep->he_htp;
	key = hep->he_kv->key;
	hashtab_lock_mod(htp, key);
	hashtab_del(&hep->he_hte);
	hashtab_unlock_mod(htp, key);
}

/*
 * Free the specified hash_exists structure.
 */
void hash_exists_free(struct existence_head *ehp)
{
	struct hash_exists *hep;
	struct keyvalue *kvp;

	hep = container_of(ehp, struct hash_exists, he_eh);
	kvp = hep->he_kv;
	if (atomic_dec_and_test(&kvp->refcnt))
		keyvalue__procon_free(kvp);
	hash_exists__procon_free(hep);
}

/*
 * Allocate and initialize a hash_exists structure as incoming,
 * which adds it to the specifried hash table.  A NULL kvp_in
 * argument allocates a new keyvalue structure with the specified
 * key and value, otherwise, the specified kvp_in keyvalue structure
 * is used and the key and value arguments are ignored.
 *
 * Returns a pointer to the hash_exists structure if successful,
 * or NULL if an entry with the specified key was already in the
 * hash table.
 */
struct hash_exists *
hash_exists_alloc(struct existence_group *egp, struct hashtab *htp,
		     struct keyvalue *kvp_in, unsigned long key,
		     unsigned long value)
{
	struct hash_exists *hep;
	struct keyvalue *kvp = kvp_in;

	hep = hash_exists__procon_alloc();
	BUG_ON(!hep);
	hep->he_htp = htp;
	if (kvp) {
		hep->he_kv = kvp;
		atomic_inc(&kvp->refcnt);
	} else {
		kvp = keyvalue__procon_alloc();
		BUG_ON(!kvp);
		kvp->key = key;
		kvp->value = value;
		atomic_set(&kvp->refcnt, 1);
		hep->he_kv = kvp;
	}
	if (existence_head_init_incoming(&hep->he_eh, egp, hash_exists_add,
				         hash_exists_remove,
				         hash_exists_free)) {
		if (atomic_dec_and_test(&kvp->refcnt))
			keyvalue__procon_unalloc(kvp);
		hash_exists__procon_unalloc(hep);
		return NULL;
	}
	return hep;
}

#endif /* #ifndef HASH_EXISTS_H */
