/*
 * hash_bkt.c: Simple hash table protected by a per-bucket lock.
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

//\begin{snippet}[labelbase=ln:datastruct:hash_bkt:struct,commandchars=\\\@\$]
/* Hash-table element to be included in structures in a hash table. */
struct ht_elem {				//\lnlbl{elem:b}
	struct cds_list_head hte_next;
	unsigned long hte_hash;
};						//\lnlbl{elem:e}

/* Hash-table bucket element. */
struct ht_bucket {				//\lnlbl{bucket:b}
	struct cds_list_head htb_head;
	spinlock_t htb_lock;
};						//\lnlbl{bucket:e}

/* Top-level hash-table data structure, including buckets. */
struct hashtab {					//\lnlbl{tab:b}
	unsigned long ht_nbuckets;
	int (*ht_cmp)(struct ht_elem *htep, void *key);
	struct ht_bucket ht_bkt[0];
};							//\lnlbl{tab:e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:datastruct:hash_bkt:map_lock,commandchars=\!\@\$]
/* Map from hash value to corresponding bucket. */
#define HASH2BKT(htp, h) /* \lnlbl{map:b} */\
	(&(htp)->ht_bkt[h % (htp)->ht_nbuckets])	//\lnlbl{map:e}

/* Underlying lock/unlock functions. */
static void hashtab_lock(struct hashtab *htp,
                         unsigned long hash)
{
	spin_lock(&HASH2BKT(htp, hash)->htb_lock);
}

static void hashtab_unlock(struct hashtab *htp,
                           unsigned long hash)
{
	spin_unlock(&HASH2BKT(htp, hash)->htb_lock);
}
//\end{snippet}

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

//\begin{snippet}[labelbase=ln:datastruct:hash_bkt:lookup,commandchars=\\\[\]]
/*
 * Look up a key.  Caller must have acquired either a read-side or update-side
 * lock via either hashtab_lock_lookup() or hashtab_lock_mod().  Note that
 * the return is a pointer to the ht_elem: Use offset_of() or equivalent
 * to get a pointer to the full data structure.
 *
 * Note that the caller is responsible for mapping from whatever type
 * of key is in use to an unsigned long, passed in via "hash".
 */
struct ht_elem *
hashtab_lookup(struct hashtab *htp, unsigned long hash,
               void *key)
{
	struct ht_bucket *htb;
	struct ht_elem   *htep;

	htb = HASH2BKT(htp, hash);			//\lnlbl{map}
	cds_list_for_each_entry(htep, &htb->htb_head, hte_next) { //\lnlbl{loop:b}
		if (htep->hte_hash != hash)		//\lnlbl{hashmatch}
			continue;			//\lnlbl{next}
		if (htp->ht_cmp(htep, key))		//\lnlbl{keymatch}
			return htep;			//\lnlbl{return}
	}						//\lnlbl{loop:e}
	return NULL;					//\lnlbl{ret_NULL}
}
//\end{snippet}

//\begin{snippet}[labelbase=ln:datastruct:hash_bkt:add_del,commandchars=\\\[\]]
/*
 * Add an element to the hash table.  Caller must have acquired the
 * update-side lock via hashtab_lock_mod().
 */
void hashtab_add(struct hashtab *htp, unsigned long hash,
                 struct ht_elem *htep)
{
	htep->hte_hash = hash;				//\lnlbl{add:set}
	cds_list_add(&htep->hte_next,			//\lnlbl{add:add:b}
	             &HASH2BKT(htp, hash)->htb_head);	//\lnlbl{add:add:e}
}

/*
 * Remove the specified element from the hash table.  Caller must have
 * acquired the update-side lock via hashtab_lock_mod().
 */
void hashtab_del(struct ht_elem *htep)
{
	cds_list_del_init(&htep->hte_next);
}
//\end{snippet}

//\begin{snippet}[labelbase=ln:datastruct:hash_bkt:alloc_free,commandchars=\\\@\$]
/*
 * Allocate a new hash table with the specified number of buckets.
 */
struct hashtab *
hashtab_alloc(unsigned long nbuckets,
              int (*cmp)(struct ht_elem *htep, void *key))
{
	struct hashtab *htp;
	int i;

	htp = malloc(sizeof(*htp) +				//\lnlbl{alloc:alloc:b}
	             nbuckets * sizeof(struct ht_bucket));	//\lnlbl{alloc:alloc:e}
	if (htp == NULL)					//\lnlbl{alloc:chk_NULL}
		return NULL;					//\lnlbl{alloc:ret_NULL}
	htp->ht_nbuckets = nbuckets;				//\lnlbl{alloc:set_nbck}
	htp->ht_cmp = cmp;					//\lnlbl{alloc:set_cmp}
	for (i = 0; i < nbuckets; i++) {			//\lnlbl{alloc:loop:b}
		CDS_INIT_LIST_HEAD(&htp->ht_bkt[i].htb_head);	//\lnlbl{alloc:init_head}
		spin_lock_init(&htp->ht_bkt[i].htb_lock);	//\lnlbl{alloc:init_lock}
	}							//\lnlbl{alloc:loop:e}
	return htp;						//\lnlbl{alloc:return}
}

/*
 * Free a hash table.  It is the caller's responsibility to ensure that it
 * is empty and no longer in use.
 */
void hashtab_free(struct hashtab *htp)			//\lnlbl{free:b}
{
	free(htp);
}							//\lnlbl{free:e}
//\end{snippet}

#ifdef TEST_HASH
#include "hashtorture.h"
#endif /* #ifdef TEST_HASH */
