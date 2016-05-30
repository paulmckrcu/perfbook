/*
 * existence_3hash_test.c: Test existence data structures for a set
 *	of three hash tables.
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

#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "../../api.h"
#define _GNU_SOURCE
#define _LGPL_SOURCE
#define RCU_SIGNAL
#include <urcu.h>
#include "existence.h"
#include "../hash/hash_bkt_rcu.c"

struct keyvalue {
	unsigned long key;
	unsigned long value;
	atomic_t refcnt;
};

struct hash_exists {
	struct ht_elem he_hte;
	struct hashtab *he_htp;
	struct existence_head he_eh;
	struct keyvalue *he_kv;
};

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
		free(kvp);
	free(hep);
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

	hep = malloc(sizeof(*hep));
	BUG_ON(!hep);
	hep->he_htp = htp;
	if (kvp) {
		hep->he_kv = kvp;
		atomic_inc(&kvp->refcnt);
	} else {
		kvp = malloc(sizeof(*kvp));
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
			free(kvp);
		free(hep);
		return NULL;
	}
	return hep;
}

/*
 * Shift values through the three hash tables, shifting in the key
 * specified by nextkey.
 */
void hash_shift(struct hashtab *htp[], unsigned long nextkey,
		struct hash_exists *hei[], struct hash_exists *heo[])
{
	struct existence_group *egp;

	egp = malloc(sizeof(*egp));
	BUG_ON(!egp);
	existence_group_init(egp);
	rcu_read_lock();
	heo[0] = hash_exists_alloc(egp, htp[0], NULL, 2 * nextkey, 2 * nextkey);
	heo[1] = hash_exists_alloc(egp, htp[1], hei[0]->he_kv, ~0, ~0);
	heo[2] = hash_exists_alloc(egp, htp[2], hei[1]->he_kv, ~0, ~0);
	BUG_ON(existence_head_set_outgoing(&hei[0]->he_eh, egp));
	BUG_ON(existence_head_set_outgoing(&hei[1]->he_eh, egp));
	BUG_ON(existence_head_set_outgoing(&hei[2]->he_eh, egp));
	rcu_read_unlock();
	existence_flip(egp);
	call_rcu(&egp->eg_rh, existence_group_rcu_cb);
}

#define HASH_SIZE 1024
struct hashtab *ht_array[3];
struct hash_exists *hei[3];
struct hash_exists *heo[3];
struct hash_exists *he_odd[3 * HASH_SIZE];

void hash_even_dump(void)
{
	struct hash_exists *hep;
	unsigned long i;
	int j;

	for (i = 0; i < 2 * HASH_SIZE; i += 2) {
		for (j = 0; j < 3; j++) {
			hep = hash_exists_lookup(ht_array[j], i);
			if (!hep)
				continue;
			printf("    %d: %4lu", j, hep->he_kv->key);
		}
	}
	printf("\n");
}

void smoketest(void)
{
	unsigned int i;
	int j;
	struct existence_group *egp;
	struct hash_exists *hep;

	egp = malloc(sizeof(*egp));
	BUG_ON(!egp);
	existence_group_init(egp);
	rcu_read_lock();
	for (i = 0; i < 3; i++) {
		ht_array[i] = hashtab_alloc(HASH_SIZE, hash_exists_cmp);
		BUG_ON(!ht_array[i]);
		hei[i] = hash_exists_alloc(egp, ht_array[i], NULL,
					   2 * (2 - i), 2 * (2 - i));
	}
	for (i = 0; i < /* HASH_SIZE */ 10; i++)
		for (j = 0; j < 3; j++)
			he_odd[3 * i + j] =
				hash_exists_alloc(egp, ht_array[j], NULL,
						  2 * i + 1, 2 * i + 1);
	rcu_read_unlock();
	existence_flip(egp);
	rcu_read_lock();
	for (i = 0; i < 3; i++)
		BUG_ON(!hash_exists_lookup(ht_array[i], 2 * (2 - i)));
	rcu_read_unlock();
	for (i = 3; i < /* HASH_SIZE */ 10; i++) {
		hash_shift(ht_array, i, hei, heo);
		rcu_read_lock();
		for (j = 0; j < 3; j++) {
			BUG_ON(!hash_exists_lookup(ht_array[j], 2 * (i - j)));
			BUG_ON(hash_exists_lookup(ht_array[j],
						  2 * (i - 1 - j)));
		}
		rcu_read_unlock();
		synchronize_rcu();
		hash_even_dump();
		for (j = 0; j < 3; j++)
			hei[j] = heo[j];
	}
	existence_group_init(egp); /* Note: synchronize_rcu() since last use. */
	rcu_read_lock();
	for (j = 0; j < 3; j++)
		BUG_ON(existence_head_set_outgoing(&hei[j]->he_eh, egp));
	for (i = 1; i < 2 * HASH_SIZE; i += 2) {
		for (j = 0; j < 3; j++) {
			hep = hash_exists_lookup(ht_array[j], i);
			if (!hep)
				continue;
			BUG_ON(existence_head_set_outgoing(&hep->he_eh, egp));
		}
	}
	rcu_read_unlock();
	existence_flip(egp);
	synchronize_rcu();
	for (i = 0; i < 2 * HASH_SIZE; i++)
		for (j = 0; j < 3; j++)
			BUG_ON(hash_exists_lookup(ht_array[j], i));

	free(egp);
	rcu_barrier();
}

int main(int argc, char *argv[])
{
	smp_init();
	rcu_register_thread();
	smoketest();

	/* Shut up unused warnings. */
	hashtab_lock_lookup(NULL, 0);
	hashtab_unlock_lookup(NULL, 0);

	rcu_unregister_thread();

	return 0;
}
