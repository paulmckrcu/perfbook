/*
 * hash_bkt_rcu.c: Simple hash table protected by a per-bucket lock for
 *	updates and RCU for lookups.
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

#define _GNU_SOURCE
#define _LGPL_SOURCE

#ifdef PERFBOOK_RCU_QSBR
#include <urcu-qsbr.h>
#else
#define RCU_SIGNAL
#include <urcu.h>
#endif

#include "../../api.h"

/* Hash-table element to be included in structures in a hash table. */
struct ht_elem {
	struct rcu_head rh;
	struct cds_list_head hte_next;
	unsigned long hte_hash;
};

/* Hash-table bucket element. */
struct ht_bucket {
	struct cds_list_head htb_head;
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

/* Underlying lock/unlock functions. */
static void hashtab_lock(struct hashtab *htp, unsigned long hash)
{
	spin_lock(&HASH2BKT(htp, hash)->htb_lock);
}

static void hashtab_unlock(struct hashtab *htp, unsigned long hash)
{
	spin_unlock(&HASH2BKT(htp, hash)->htb_lock);
}

//\begin{snippet}[labelbase=ln:datastruct:hash_bkt_rcu:lock_unlock,commandchars=\\\[\]]
/* Read-side lock/unlock functions. */
static void hashtab_lock_lookup(struct hashtab *htp,
                                unsigned long hash)
{
	rcu_read_lock();
}

static void hashtab_unlock_lookup(struct hashtab *htp,
                                  unsigned long hash)
{
	rcu_read_unlock();
}
//\end{snippet}

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

//\begin{snippet}[labelbase=ln:datastruct:hash_bkt_rcu:lookup,commandchars=\\\[\]]
/*
 * Look up a key.  Caller must have acquired either a read-side or update-side
 * lock via either hashtab_lock_lookup() or hashtab_lock_mod().  Note that
 * the return is a pointer to the ht_elem: Use offset_of() or equivalent
 * to get a pointer to the full data structure.
 *
 * Note that the caller is responsible for mapping from whatever type
 * of key is in use to an unsigned long, passed in via "hash".
 */
struct ht_elem *hashtab_lookup(struct hashtab *htp,
                               unsigned long hash,
                               void *key)
{
	struct ht_bucket *htb;
	struct ht_elem  *htep;

	htb = HASH2BKT(htp, hash);
	cds_list_for_each_entry_rcu(htep,
	                            &htb->htb_head,
	                            hte_next) {
		if (htep->hte_hash != hash)
			continue;
		if (htp->ht_cmp(htep, key))
			return htep;
	}
	return NULL;
}
//\end{snippet}

//\begin{snippet}[labelbase=ln:datastruct:hash_bkt_rcu:add_del,commandchars=\\\[\]]
/*
 * Add an element to the hash table.  Caller must have acquired the
 * update-side lock via hashtab_lock_mod().
 */
void hashtab_add(struct hashtab *htp,
                 unsigned long hash,
                 struct ht_elem *htep)
{
	htep->hte_hash = hash;
	cds_list_add_rcu(&htep->hte_next,
	                 &HASH2BKT(htp, hash)->htb_head);
}

/*
 * Remove the specified element from the hash table.  Caller must have
 * acquired the update-side lock via hashtab_lock_mod().
 */
void hashtab_del(struct ht_elem *htep)
{
	cds_list_del_rcu(&htep->hte_next);
}
//\end{snippet}

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
	for (i = 0; i < nbuckets; i++) {
		CDS_INIT_LIST_HEAD(&htp->ht_bkt[i].htb_head);
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

#define hash_register_thread() rcu_register_thread()
#define hash_unregister_thread() rcu_unregister_thread()

void (*defer_del_done)(struct ht_elem *htep) = NULL;

void defer_del_rcu(struct rcu_head *rhp)
{
	defer_del_done((struct ht_elem *)rhp);
}

#define defer_del(p)	call_rcu(&(p)->rh, defer_del_rcu)

#define quiescent_state() rcu_quiescent_state()

#ifdef TEST_HASH
#include "hashtorture.h"
#endif /* #ifdef TEST_HASH */
