/*
 * existence_3skiplist_test.c: Test existence data structures for a set
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
#include "existence.h"
#include "keyvalue.h"
#include "skiplist_exists.h"

/*
 * Shift values through the three skiplists, shifting in the key
 * specified by nextkey.
 */
void skiplist_shift(struct skiplist slhp[], unsigned long nextkey,
		    struct skiplist_exists *sei[],
		    struct skiplist_exists *seo[])
{
	struct existence_group *egp;

	egp = malloc(sizeof(*egp));
	BUG_ON(!egp);
	existence_group_init(egp);
	rcu_read_lock();
	seo[0] = skiplist_exists_alloc(egp, &slhp[0], NULL,
				       2 * nextkey, 2 * nextkey);
	seo[1] = skiplist_exists_alloc(egp, &slhp[1], sei[0]->se_kv, ~0, ~0);
	seo[2] = skiplist_exists_alloc(egp, &slhp[2], sei[1]->se_kv, ~0, ~0);
	BUG_ON(existence_head_set_outgoing(&sei[0]->se_eh, egp));
	BUG_ON(existence_head_set_outgoing(&sei[1]->se_eh, egp));
	BUG_ON(existence_head_set_outgoing(&sei[2]->se_eh, egp));
	rcu_read_unlock();
	existence_flip(egp);
	call_rcu(&egp->eg_rh, existence_group_rcu_cb);
}

#define N_ELEMS 1024
struct skiplist sl_array[3];
struct skiplist_exists *sei[3];
struct skiplist_exists *seo[3];
struct skiplist_exists *se_odd[3 * N_ELEMS];

void skiplist_even_dump(void)
{
	struct skiplist_exists *slep;
	unsigned long i;
	int j;

	for (i = 0; i < 2 * N_ELEMS; i += 2) {
		for (j = 0; j < 3; j++) {
			slep = skiplist_exists_lookup(&sl_array[j], i);
			if (!slep)
				continue;
			printf("    %d: %4lu", j, slep->se_kv->key);
		}
	}
	printf("\n");
}

void smoketest(void)
{
	unsigned int i;
	int j;
	struct existence_group *egp;
	struct skiplist_exists *slep;

	egp = malloc(sizeof(*egp));
	BUG_ON(!egp);
	existence_group_init(egp);
	rcu_read_lock();
	for (i = 0; i < 3; i++) {
		skiplist_init(&sl_array[i], skiplist_exists_cmp);
		sei[i] = skiplist_exists_alloc(egp, &sl_array[i], NULL,
					       2 * (2 - i), 2 * (2 - i));
	}
	for (i = 0; i < /* N_ELEMS */ 10; i++)
		for (j = 0; j < 3; j++)
			se_odd[3 * i + j] =
				skiplist_exists_alloc(egp, &sl_array[j], NULL,
						      2 * i + 1, 2 * i + 1);
	rcu_read_unlock();
	existence_flip(egp);
	rcu_read_lock();
	for (i = 0; i < 3; i++)
		BUG_ON(!skiplist_exists_lookup(&sl_array[i], 2 * (2 - i)));
	rcu_read_unlock();
	for (i = 3; i < /* N_ELEMS */ 10; i++) {
		skiplist_shift(sl_array, i, sei, seo);
		rcu_read_lock();
		for (j = 0; j < 3; j++) {
			BUG_ON(!skiplist_exists_lookup(&sl_array[j],
						       2 * (i - j)));
			BUG_ON(skiplist_exists_lookup(&sl_array[j],
						      2 * (i - 1 - j)));
		}
		rcu_read_unlock();
		synchronize_rcu();
		skiplist_even_dump();
		for (j = 0; j < 3; j++)
			sei[j] = seo[j];
	}
	existence_group_init(egp); /* Note: synchronize_rcu() since last use. */
	rcu_read_lock();
	for (j = 0; j < 3; j++)
		BUG_ON(existence_head_set_outgoing(&sei[j]->se_eh, egp));
	for (i = 1; i < 2 * N_ELEMS; i += 2) {
		for (j = 0; j < 3; j++) {
			slep = skiplist_exists_lookup(&sl_array[j], i);
			if (!slep)
				continue;
			BUG_ON(existence_head_set_outgoing(&slep->se_eh, egp));
		}
	}
	rcu_read_unlock();
	existence_flip(egp);
	synchronize_rcu();
	for (i = 0; i < 2 * N_ELEMS; i++)
		for (j = 0; j < 3; j++)
			BUG_ON(skiplist_exists_lookup(&sl_array[j], i));

	free(egp);
	rcu_barrier();
}

int main(int argc, char *argv[])
{
	smp_init();
	rcu_register_thread();
	existence_group__procon_init();
	keyvalue__procon_init();
	skiplist_exists__procon_init();
	smoketest();
	rcu_unregister_thread();

	return 0;
}
