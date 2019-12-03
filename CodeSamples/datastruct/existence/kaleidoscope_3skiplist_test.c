/*
 * kaleidoscope_3skiplist_test.c: Test kaleidoscopic data structures for a set
 *	of three skiplists.
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
#include "../skiplist/skiplist.c"

#include "procon.h"
#include "kaleidoscope.h"
#include "keyvalue.h"
#include "skiplist_kaleid.h"

#define N_ELEMS 1024
struct skiplist sl_array[3];
struct skiplist_kaleid *skperm[3]; /* Permanent entries, key == 10. */
struct skiplist_kaleid *skstate[3 * 3]; /* State-varying entries, key == idx. */

void skiplist_dump_ten(void)
{
	struct skiplist_kaleid *skp;
	unsigned long i;
	int j;

	rcu_read_lock();
	for (i = 0; i <= 10; i++) {
		for (j = 0; j < 3; j++) {
			skp = skiplist_kaleid_lookup(&sl_array[j], i);
			if (!skp)
				continue;
			printf("    %d: %lu", j, skp->sk_kv->key);
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
		skiplist_init(&sl_array[i], skiplist_kaleid_cmp);
		skperm[i] = skiplist_kaleid_alloc(NULL, &sl_array[i], NULL, 0,
						  10, 10);
	}
	for (i = 0; i < 3; i++)
		for (j = 0; j < 3; j++)
			skstate[3 * i + j] =
				skiplist_kaleid_alloc(kgp, &sl_array[i], NULL,
						      j, 3 * i + j, 3 * i + j);
	printf("Initial state:\n");
	skiplist_dump_ten();
	rcu_read_unlock();
	for (k = 0; k < 3; k++) {
		printf("State %d:\n", k);
		kaleidoscope_set_state(kgp, k);
		skiplist_dump_ten();
		for (i = 0; i < 3; i++) {
			rcu_read_lock();
			BUG_ON(!skiplist_kaleid_lookup(&sl_array[i], 10));
			for (j = 0; j < 3; j++) {
				BUG_ON(!!skiplist_kaleid_lookup(&sl_array[k],
							    3 * i + j) !=
				       (i == k && k == j));
			}
			rcu_read_unlock();
		}
	}
	printf("Commit to current state:\n");
	kaleidoscope_commit(kgp);
	skiplist_dump_ten();
	for (i = 0; i < 3; i++) {
		rcu_read_lock();
		BUG_ON(!skiplist_kaleid_lookup(&sl_array[i], 10));
		for (j = 0; j < 3; j++) {
			BUG_ON(!!skiplist_kaleid_lookup(&sl_array[0],
							3 * i + j) !=
			       (i == 0 && j == 2));
			BUG_ON(!!skiplist_kaleid_lookup(&sl_array[1],
							3 * i + j) !=
			       (i == 1 && j == 2));
			BUG_ON(!!skiplist_kaleid_lookup(&sl_array[2],
							3 * i + j) !=
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
	skiplist_kaleid__procon_init();
	smoketest();
	rcu_unregister_thread();

	return 0;
}
