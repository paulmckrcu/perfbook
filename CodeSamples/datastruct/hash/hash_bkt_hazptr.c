/*
 * hash_bkt_hazptr.c: Simple hash table protected by a per-bucket lock for
 *	updates and hazard pointers for lookups.
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

#include "../../defer/hazptr.h"

/*
 * Hash-table element to be included at the beginning of structures in
 * a hash table.
 */
struct ht_elem {
	hazptr_head_t hh;
	struct ht_elem *hte_next;
	struct ht_elem *hte_prev;
	unsigned long hte_hash;
};

/* Hash-table bucket element. */
struct ht_bucket {
	struct ht_elem htb_head;
	spinlock_t htb_lock;
};

/* Top-level hash-table data structure, including buckets. */
struct hashtab {
	unsigned long ht_nbuckets;
	int (*ht_cmp)(struct ht_elem *htep, void *key);
	struct ht_bucket ht_bkt[0];
};

/* Map from hash value to corresponding bucket. */
#define HASH2BKT(htp, h) (&(htp)->ht_bkt[h % (htp)->ht_nbuckets])

/* This thread's fixed-sized set of hazard pointers. */
hazard_pointer __thread *my_hazptr;

/* Underlying lock/unlock functions. */
static void hashtab_lock(struct hashtab *htp, unsigned long hash)
{
	spin_lock(&HASH2BKT(htp, hash)->htb_lock);
}

static void hashtab_unlock(struct hashtab *htp, unsigned long hash)
{
	spin_unlock(&HASH2BKT(htp, hash)->htb_lock);
}

/* Read-side lock/unlock functions, empty for hazard pointers. */
static void hashtab_lock_lookup(struct hashtab *htp, unsigned long hash)
{
}

static void hashtab_unlock_lookup(struct hashtab *htp, unsigned long hash)
{
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
	struct ht_elem *htep_head;
	struct ht_elem **htepp = NULL;
	int offset = 0;

	/*
	 * If hazard-pointer acquisition races with an update, it is
	 * necessary to start from the beginning.  The reason for this
	 * is that hazard-pointer protection is on a strict per-element
	 * basis.  Therefore, once someone deletes an element out from
	 * under us, they might well delete subsequent elements before
	 * we can hazard-pointer them, so we cannot trust the remainder
	 * of the list and must instead start over.
	 */
retry:
	htep_head = &HASH2BKT(htp, hash)->htb_head;
	htepp = &htep_head->hte_next;
	do {
		/* Pick up a pointer and check for end of list. */
		htep = ACCESS_ONCE(*htepp);
		if (htep == htep_head)
			return NULL;
		if (htep == (struct ht_elem *)HAZPTR_POISON)
			goto retry;  /* Element was deleted. */

		/* Store a hazard pointer. */
		my_hazptr[offset].p = &htep->hh;
		offset = !offset;
		smp_mb(); /* Force pointer loads in order. */

		/* Recheck the hazard pointer against the original. */
		if (ACCESS_ONCE(*htepp) != htep)
			goto retry;

		/* Advance to next. */
		htepp = &htep->hte_next;
	} while (htep->hte_hash != hash && !htp->ht_cmp(htep, key));
	return htep;
}

/*
 * Add an element to the hash table.  Caller must have acquired the
 * update-side lock via hashtab_lock_mod().
 */
void hashtab_add(struct hashtab *htp, unsigned long hash, struct ht_elem *htep)
{
	struct ht_elem *prev = &HASH2BKT(htp, hash)->htb_head;
	struct ht_elem *next = prev->hte_next;

	htep->hte_hash = hash;
	htep->hte_next = next;
	htep->hte_prev = prev;
	next->hte_prev = htep;
	smp_mb(); /* Initialize element before publishing it. */
	ACCESS_ONCE(prev->hte_next) = htep;
}

/*
 * Remove the specified element from the hash table.  Caller must have
 * acquired the update-side lock via hashtab_lock_mod().
 *
 * Note that -both- pointers are poisoned.  The reason for poisoning
 * the ->hte_next pointer is to allow hashtab_lookup() to detect when
 * an element has been deleted in order to avoid traversing the
 * remainder of the list, which might well have been not only deleted,
 * but also freed.
 */
void hashtab_del(struct ht_elem *htep)
{
	htep->hte_next->hte_prev = htep->hte_prev;
	ACCESS_ONCE(htep->hte_prev->hte_next) = htep->hte_next;
	smp_mb(); /* Ensure element is skipped before pointers are poisoned. */
	htep->hte_prev = (struct ht_elem *)HAZPTR_POISON;
	htep->hte_next = (struct ht_elem *)HAZPTR_POISON;
}

/*
 * Allocate a new hash table with the specified number of buckets.
 */
struct hashtab *hashtab_alloc(unsigned long nbuckets,
			      int (*cmp)(struct ht_elem *htep, void *key))
{
	struct ht_elem *htep;
	struct hashtab *htp;
	int i;

	htp = malloc(sizeof(*htp) + nbuckets * sizeof(struct ht_bucket));
	if (htp == NULL)
		return NULL;
	htp->ht_nbuckets = nbuckets;
	htp->ht_cmp = cmp;
	for (i = 0; i < nbuckets; i++) {
		htep = &htp->ht_bkt[i].htb_head;
		htep->hte_next = htep;
		htep->hte_prev = htep;
		spin_lock_init(&htp->ht_bkt[i].htb_lock);
	}
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

void hash_register_thread(void)
{
	my_hazptr = &HP[K * smp_thread_id()];
}
#define hash_register_thread hash_register_thread

#define hash_unregister_thread() hazptr_thread_exit()

void (*defer_del_done)(struct ht_elem *) = NULL;

void hazptr_free(void *p)
{
	defer_del_done((struct ht_elem *)p);
}

#define defer_del(p)	hazptr_free_later(&(p)->hh);
#define other_init()	hazptr_init()

#ifdef TEST_HASH
#include "hashtorture.h"
#endif /* #ifdef TEST_HASH */
