/*
 * kaleidoscope_3hash_test.c: Test kaleidoscopic data structures for a set
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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
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
#include "../hash/hash_bkt_rcu.c"

#include "procon.h"
#include "kaleidoscope.h"
#include "keyvalue.h"
#include "hash_kaleid.h"

#define HASH_SIZE 1024
struct hashtab *ht_array[3];
struct hash_kaleid *hkperm[3]; /* Permanent entries, key == 10. */
struct hash_kaleid *hkstate[3 * 3]; /* State-controlled entries, key == idx. */

void hash_dump_ten(void)
{
	struct hash_kaleid *hkp;
	unsigned long i;
	int j;

	rcu_read_lock();
	for (i = 0; i <= 10; i++) {
		for (j = 0; j < 3; j++) {
			hkp = hash_kaleid_lookup(ht_array[j], i);
			if (!hkp)
				continue;
			printf("    %d: %lu", j, hkp->hk_kv->key);
		}
	}
	printf("\n");
	rcu_read_unlock();
}

void smoketest(void)
{
	unsigned int i;
	int j;
	int k;
	struct kaleidoscope_group *kgp;

	kgp = malloc(sizeof(*kgp));
	BUG_ON(!kgp);
	kaleidoscope_group_init(kgp);
	rcu_read_lock();
	for (i = 0; i < 3; i++) {
		ht_array[i] = hashtab_alloc(HASH_SIZE, hash_kaleid_cmp);
		BUG_ON(!ht_array[i]);
		hkperm[i] = hash_kaleid_alloc(NULL, ht_array[i], NULL, 0,
					      10, 10);
	}
	for (i = 0; i < 3; i++)
		for (j = 0; j < 3; j++)
			hkstate[3 * i + j] =
				hash_kaleid_alloc(kgp, ht_array[i], NULL, j,
						  3 * i + j, 3 * i + j);
	printf("Initial state:\n");
	hash_dump_ten();
	rcu_read_unlock();
	for (k = 0; k < 3; k++) {
		printf("State %d:\n", k);
		kaleidoscope_set_state(kgp, k);
		hash_dump_ten();
		for (i = 0; i < 3; i++) {
			rcu_read_lock();
			BUG_ON(!hash_kaleid_lookup(ht_array[i], 10));
			for (j = 0; j < 3; j++) {
				BUG_ON(!!hash_kaleid_lookup(ht_array[k],
							    3 * i + j) !=
				       (i == k && k == j));
			}
			rcu_read_unlock();
		}
	}
	printf("Commit to current state:\n");
	kaleidoscope_commit(kgp);
	hash_dump_ten();
	for (i = 0; i < 3; i++) {
		rcu_read_lock();
		BUG_ON(!hash_kaleid_lookup(ht_array[i], 10));
		for (j = 0; j < 3; j++) {
			BUG_ON(!!hash_kaleid_lookup(ht_array[0], 3 * i + j) !=
			       (i == 0 && j == 2));
			BUG_ON(!!hash_kaleid_lookup(ht_array[1], 3 * i + j) !=
			       (i == 1 && j == 2));
			BUG_ON(!!hash_kaleid_lookup(ht_array[2], 3 * i + j) !=
			       (i == 2 && j == 2));
		}
		rcu_read_unlock();
	}
	synchronize_rcu();
	rcu_barrier();
	free(kgp);
}

int main(int argc, char *argv[])
{
	smp_init();
	rcu_register_thread();
	kaleidoscope_group__procon_init();
	keyvalue__procon_init();
	hash_kaleid__procon_init();
	smoketest();

	/* Shut up unused warnings. */
	hashtab_lock_lookup(NULL, 0);
	hashtab_unlock_lookup(NULL, 0);

	rcu_unregister_thread();

	return 0;
}
