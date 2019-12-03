/*
 * hash_global.c: Simple hash table protected by a global lock.
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
 * Copyright (c) 2013-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#define _LGPL_SOURCE
#include "../../api.h"

/* Hash-table element to be included in structures in a hash table. */
struct ht_elem {
	struct cds_list_head hte_next;
	unsigned long hte_hash;
};

/* Hash-table bucket element. */
struct ht_bucket {
	struct cds_list_head htb_head;
};

/* Top-level hash-table data structure, including buckets. */
struct hashtab {
	unsigned long ht_nbuckets;
	spinlock_t ht_lock;
	int (*ht_cmp)(struct ht_elem *htep, void *key);
	struct ht_bucket ht_bkt[0];
};

/* Map from hash value to corresponding bucket. */
#define HASH2BKT(htp, h) (&(htp)->ht_bkt[h % (htp)->ht_nbuckets])

/* Underlying lock/unlock functions. */
static void hashtab_lock(struct hashtab *htp, unsigned long hash)
{
	spin_lock(&htp->ht_lock);
}

static void hashtab_unlock(struct hashtab *htp, unsigned long hash)
{
	spin_unlock(&htp->ht_lock);
}

/* Read-side lock/unlock functions. */
static void hashtab_lock_lookup(struct hashtab *htp, unsigned long hash)
{
	hashtab_lock(htp, hash);
}

static void hashtab_unlock_lookup(struct hashtab *htp, unsigned long hash)
{
	hashtab_unlock(htp, hash);
}

/* Update-side lock/unlock functions. */
static void hashtab_lock_mod(struct hashtab *htp, unsigned long hash)
{
	hashtab_lock(htp, hash);
}

static void hashtab_unlock_mod(struct hashtab *htp, unsigned long hash)
{
	hashtab_unlock(htp, hash);
}

/*
 * Finished using a looked up hashtable element.
 */
void hashtab_lookup_done(struct ht_elem *htep)
{
}

/*
 * Look up a key.  Caller must have acquired either a read-side or update-side
 * lock via either hashtab_lock_lookup() or hashtab_lock_mod().  Note that
 * the return is a pointer to the ht_elem: Use offset_of() or equivalent
 * to get a pointer to the full data structure.
 *
 * Note that the caller is responsible for mapping from whatever type
 * of key is in use to an unsigned long, passed in via "hash".
 */
struct ht_elem *hashtab_lookup(struct hashtab *htp, unsigned long hash,
			       void *key)
{
	struct ht_elem *htep;

	cds_list_for_each_entry(htep,
				&HASH2BKT(htp, hash)->htb_head,
				hte_next) {
		if (htep->hte_hash != hash)
			continue;
		if (htp->ht_cmp(htep, key))
			return htep;
	}
	return NULL;
}

/*
 * Add an element to the hash table.  Caller must have acquired the
 * update-side lock via hashtab_lock_mod().
 */
void hashtab_add(struct hashtab *htp, unsigned long hash, struct ht_elem *htep)
{
	htep->hte_hash = hash;
	cds_list_add(&htep->hte_next, &HASH2BKT(htp, hash)->htb_head);
}

/*
 * Remove the specified element from the hash table.  Caller must have
 * acquired the update-side lock via hashtab_lock_mod().
 */
void hashtab_del(struct ht_elem *htep)
{
	cds_list_del_init(&htep->hte_next);
}

/*
 * Allocate a new hash table with the specified number of buckets.
 */
struct hashtab *hashtab_alloc(unsigned long nbuckets,
			      int (*cmp)(struct ht_elem *htep, void *key))
{
	struct hashtab *htp;
	int i;

	htp = malloc(sizeof(*htp) + nbuckets * sizeof(struct ht_bucket));
	if (htp == NULL)
		return NULL;
	htp->ht_nbuckets = nbuckets;
	htp->ht_cmp = cmp;
	spin_lock_init(&htp->ht_lock);
	for (i = 0; i < nbuckets; i++)
		CDS_INIT_LIST_HEAD(&htp->ht_bkt[i].htb_head);
	return htp;
}

/*
 * Free a hash table.  It is the caller's responsibility to ensure that it
 * is empty and no longer in use.
 */
void hashtab_free(struct hashtab *htp)
{
	free(htp);
}

#ifdef TEST_HASH
#include "hashtorture.h"
#endif /* #ifdef TEST_HASH */
