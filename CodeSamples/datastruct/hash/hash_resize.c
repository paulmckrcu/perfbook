/*
 * hash_resize.c: Resizable hash table protected by a per-bucket lock for
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
 * Copyright (c) 2013 Paul E. McKenney, IBM Corporation.
 */

#define _GNU_SOURCE
#define _LGPL_SOURCE
#define RCU_SIGNAL
#include <urcu.h>
#include "../../api.h"

/* Hash-table element to be included in structures in a hash table. */
struct ht_elem {
	struct rcu_head rh;
	struct cds_list_head hte_next[2];
	unsigned long hte_hash;
};

/* Hash-table bucket element. */
struct ht_bucket {
	struct cds_list_head htb_head;
	spinlock_t htb_lock;
};

/* Hash-table instance, duplicated at resize time. */
struct ht {
	long ht_nbuckets;
	long ht_resize_cur;
	struct ht *ht_new;
	int ht_idx;
	void *ht_hash_private;
	int (*ht_cmp)(void *hash_private, struct ht_elem *htep, void *key);
	long (*ht_gethash)(void *hash_private, void *key);
	void *(*ht_getkey)(struct ht_elem *htep);
	struct ht_bucket ht_bkt[0];
};

/* Top-level hash-table data structure, including buckets. */
struct hashtab {
	struct ht *ht_cur;
	spinlock_t ht_lock;
};

/* Allocate a hash-table instance. */
struct ht *
ht_alloc(unsigned long nbuckets, void *hash_private,
	 int (*cmp)(void *hash_private, struct ht_elem *htep, void *key),
	 long (*gethash)(void *hash_private, void *key),
	 void *(*getkey)(struct ht_elem *htep))
{
	struct ht *htp;
	int i;

	htp = malloc(sizeof(*htp) + nbuckets * sizeof(struct ht_bucket));
	if (htp == NULL)
		return NULL;
	htp->ht_nbuckets = nbuckets;
	htp->ht_resize_cur = -1;
	htp->ht_new = NULL;
	htp->ht_idx = 0;
	htp->ht_hash_private = hash_private;
	htp->ht_cmp = cmp;
	htp->ht_gethash = gethash;
	htp->ht_getkey = getkey;
	for (i = 0; i < nbuckets; i++) {
		CDS_INIT_LIST_HEAD(&htp->ht_bkt[i].htb_head);
		spin_lock_init(&htp->ht_bkt[i].htb_lock);
	}
	return htp;
}

/* Allocate a full hash table, master plus instance. */
struct hashtab *
hashtab_alloc(unsigned long nbuckets, void *hash_private,
	      int (*cmp)(void *hash_private, struct ht_elem *htep, void *key),
	      long (*gethash)(void *hash_private, void *key),
	      void *(*getkey)(struct ht_elem *htep))
{
	struct hashtab *htp_master;

	htp_master = malloc(sizeof(*htp_master));
	if (htp_master == NULL)
		return NULL;
	htp_master->ht_cur =
		ht_alloc(nbuckets, hash_private, cmp, gethash, getkey);
	if (htp_master->ht_cur == NULL) {
		free(htp_master);
		return NULL;
	}
	spin_lock_init(&htp_master->ht_lock);
	return htp_master;
}

/* Free a full hash table, master plus instance. */
void hashtab_free(struct hashtab *htp_master)
{
	free(htp_master->ht_cur);
	free(htp_master);
}

/* Get hash bucket corresponding to key, ignoring the possibility of resize. */
static struct ht_bucket *
ht_get_bucket_single(struct ht *htp, void *key, long *b)
{
	*b = htp->ht_gethash(htp->ht_hash_private, key) % htp->ht_nbuckets;
	return &htp->ht_bkt[*b];
}

/* Get hash bucket correesponding to key, accounting for resize. */
static struct ht_bucket *ht_get_bucket(struct ht **htp, void *key, long *b, int *i)
{
	struct ht_bucket *htbp = ht_get_bucket_single(*htp, key, b);

	if (*b <= (*htp)->ht_resize_cur) {
		smp_mb(); /* order ->ht_resize_cur before ->ht_new. */
		*htp = (*htp)->ht_new;
		htbp = ht_get_bucket_single(*htp, key, b);
	}
	if (i)
		*i = (*htp)->ht_idx;
	return htbp;
}

/* Read-side lock/unlock functions. */
static void hashtab_lock_lookup(struct hashtab *htp_master, void *key)
{
	rcu_read_lock();
}

static void hashtab_unlock_lookup(struct hashtab *htp_master, void *key)
{
	rcu_read_unlock();
}

/* Update-side lock/unlock functions. */
static void hashtab_lock_mod(struct hashtab *htp_master, void *key)
{
	long b;
	struct ht *htp;
	struct ht_bucket *htbp;
	struct ht_bucket *htbp_new;

	rcu_read_lock();
	htp = rcu_dereference(htp_master->ht_cur);
	htbp = ht_get_bucket_single(htp, key, &b);
	spin_lock(&htbp->htb_lock);
	if (b > htp->ht_resize_cur)
		return;
	htp = htp->ht_new;
	htbp_new = ht_get_bucket_single(htp, key, &b);
	spin_lock(&htbp_new->htb_lock);
	spin_unlock(&htbp->htb_lock);
}

static void hashtab_unlock_mod(struct hashtab *htp_master, void *key)
{
	long b;
	struct ht *htp = rcu_dereference(htp_master->ht_cur);
	struct ht_bucket *htbp = ht_get_bucket(&htp, key, &b, NULL);

	spin_unlock(&htbp->htb_lock);
	rcu_read_unlock();
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
 */
struct ht_elem *hashtab_lookup(struct hashtab *htp_master, void *key)
{
	long b;
	int i;
	struct ht *htp = rcu_dereference(htp_master->ht_cur);
	struct ht_elem *htep;
	struct ht_bucket *htbp = ht_get_bucket(&htp, key, &b, &i);

	cds_list_for_each_entry_rcu(htep, &htbp->htb_head, hte_next[i]) {
		if (htp->ht_cmp(htp->ht_hash_private, htep, key))
			return htep;
	}
	return NULL;
}

/*
 * Add an element to the hash table.  Caller must have acquired the
 * update-side lock via hashtab_lock_mod().
 */
void hashtab_add(struct hashtab *htp_master, struct ht_elem *htep)
{
	long b;
	int i;
	struct ht *htp = rcu_dereference(htp_master->ht_cur);
	struct ht_bucket *htbp = ht_get_bucket(&htp, htp->ht_getkey(htep),
					       &b, &i);

	cds_list_add_rcu(&htep->hte_next[i], &htbp->htb_head);
}

/*
 * Remove the specified element from the hash table.  Caller must have
 * acquired the update-side lock via hashtab_lock_mod().
 */
void hashtab_del(struct hashtab *htp_master, struct ht_elem *htep)
{
	long b;
	int i;
	struct ht *htp = rcu_dereference(htp_master->ht_cur);

	(void)ht_get_bucket(&htp, htp->ht_getkey(htep), &b, &i);
	cds_list_del_rcu(&htep->hte_next[i]);
}

/* Resize a hash table. */
int
hashtab_resize(struct hashtab *htp_master,
	       unsigned long nbuckets, void *hash_private,
	       int (*cmp)(void *hash_private, struct ht_elem *htep, void *key),
	       long (*gethash)(void *hash_private, void *key),
	       void *(*getkey)(struct ht_elem *htep))
{
	struct ht *htp;
	struct ht *htp_new;
	int i;
	int idx;
	struct ht_elem *htep;
	struct ht_bucket *htbp;
	struct ht_bucket *htbp_new;
	long b;

	if (!spin_trylock(&htp_master->ht_lock))
		return -EBUSY;
	htp = htp_master->ht_cur;
	htp_new = ht_alloc(nbuckets,
			   hash_private ? hash_private : htp->ht_hash_private,
			   cmp ? cmp : htp->ht_cmp,
			   gethash ? gethash : htp->ht_gethash,
			   getkey ? getkey : htp->ht_getkey);
	if (htp_new == NULL) {
		spin_unlock(&htp_master->ht_lock);
		return -ENOMEM;
	}
	htp->ht_new = htp_new;
	synchronize_rcu();
	idx = htp->ht_idx;
	htp_new->ht_idx = !idx;
	for (i = 0; i < htp->ht_nbuckets; i++) {
		htbp = &htp->ht_bkt[i];
		spin_lock(&htbp->htb_lock);
		htp->ht_resize_cur = i;
		cds_list_for_each_entry(htep, &htbp->htb_head, hte_next[idx]) {
			htbp_new =
				ht_get_bucket_single(htp_new,
						     htp_new->ht_getkey(htep),
						     &b);
			spin_lock(&htbp_new->htb_lock);
			cds_list_add_rcu(&htep->hte_next[!idx],
					 &htbp_new->htb_head);
			spin_unlock(&htbp_new->htb_lock);
		}
		spin_unlock(&htbp->htb_lock);
	}
	rcu_assign_pointer(htp_master->ht_cur, htp_new);
	synchronize_rcu();
	spin_unlock(&htp_master->ht_lock);
	free(htp);
	return 0;
}

/* Test functions. */
long tgh(void *hash_private, void *key)
{
	return (long)key;
}

int testcmp(struct ht_elem *htep, void *key);

int tc(void *hash_private, struct ht_elem *htep, void *key)
{
	return testcmp(htep, key);
}

struct hashtab *test_htp;

#define hashtab_alloc(n, cmp) hashtab_alloc((n), NULL, tc, tgh, testgk)
#define hash_register_test(htp) do test_htp = (htp); while (0)
#define hash_register_thread() rcu_register_thread()
#define hash_unregister_thread() rcu_unregister_thread()
#define hashtab_lock_lookup(htp, i) hashtab_lock_lookup((htp), (void *)(i))
#define hashtab_unlock_lookup(htp, i) hashtab_unlock_lookup((htp), (void *)(i))
#define hashtab_lock_mod(htp, i) hashtab_lock_mod((htp), (void *)(i))
#define hashtab_unlock_mod(htp, i) hashtab_unlock_mod((htp), (void *)(i))
#define hashtab_lookup(htp, h, k) hashtab_lookup((htp), (k))
#define hashtab_add(htp, h, htep) hashtab_add((htp), (htep))
#define hashtab_del(htep) hashtab_del(test_htp, (htep))
#define hash_resize_test(htp, n) hashtab_resize((htp), (n), (void *)1, NULL, NULL, NULL)

void (*defer_del_done)(struct ht_elem *htep) = NULL;

void defer_del_rcu(struct rcu_head *rhp)
{
	defer_del_done((struct ht_elem *)rhp);
}

#ifdef TEST_HASH
#define defer_del(p)	call_rcu(&(p)->rh, defer_del_rcu)

#define quiescent_state() rcu_quiescent_state()

#include "hashtorture.h"
#endif /* #ifdef TEST_HASH */
