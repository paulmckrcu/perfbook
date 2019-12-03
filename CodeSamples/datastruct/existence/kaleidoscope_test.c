/*
 * kaleidoscope_test.c: Test kaleidoscope data structures.
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

#include "procon.h"
#include "kaleidoscope.h"

struct kaleid_test {
	struct kaleidoscope_head kt_kh;
	int kt_added;
	int kt_removed;
	int kt_freed;
};

struct kaleidoscope_group kg;

struct kaleid_test states[KALEID_N_STATES];
struct kaleid_test perm;

static void kaleid_test_init(struct kaleid_test *ktp)
{
	ktp->kt_added = 0;
	ktp->kt_removed = 0;
	ktp->kt_freed = 0;
}

static int kaleid_test_add(struct kaleidoscope_head *khp)
{
	struct kaleid_test *ktp = container_of(khp, struct kaleid_test, kt_kh);

	ktp->kt_added = 1;
	return 0;
}

static void kaleid_test_remove(struct kaleidoscope_head *khp)
{
	struct kaleid_test *ktp = container_of(khp, struct kaleid_test, kt_kh);

	ktp->kt_removed = 1;
}

static void kaleid_test_free(struct kaleidoscope_head *khp)
{
	struct kaleid_test *ktp = container_of(khp, struct kaleid_test, kt_kh);

	ktp->kt_freed = 1;
}

static void dump_kaleidoscope_group(struct kaleidoscope_group *kgp)
{
	struct kaleidoscope_head *khp;
	int i;

	printf("Kaleidoscope group %p  state: %lu\n",  kgp, kgp->kg_state);
	for (i = 0; i < KALEID_N_STATES; i++) {
		printf("\tState %d:", i);
		cds_list_for_each_entry(khp, &kgp->kg_statelist[i], kh_list)
			printf(" %p", khp);
		printf("\n");
	}
}

static void dump_kaleidoscope_head(struct kaleidoscope_head *khp)
{
	printf("Kaleidoscope head %p egi: %#lx  %c%c add: %p remove: %p free: %p\n",
	       khp, khp->kh_kgi,
	       "L."[!!cds_list_empty(&khp->kh_list)],
	       ".G"[!!khp->kh_gone],
	       khp->kh_add, khp->kh_remove, khp->kh_free);
}

static void dump_kaleid_test(struct kaleid_test *ktp)
{
	dump_kaleidoscope_head(&ktp->kt_kh);
	printf("\t%s %s %s\n",
	       ktp->kt_added ? "added" : "unadded",
	       ktp->kt_removed ? "removed" : "unremoved",
	       ktp->kt_freed ? "freed" : "unfreed");
}

static void dump_all(void)
{
	int i;

	dump_kaleidoscope_group(&kg);
	printf("perm: ");
	dump_kaleid_test(&perm);
	for (i = 0; i < KALEID_N_STATES; i++) {
		printf("State %d: ", i);
		dump_kaleid_test(&states[i]);
	}
}

void setup(void)
{
	int i;
	int ret;

	kaleidoscope_group_init(&kg);
	dump_kaleidoscope_group(&kg);

	kaleid_test_init(&perm);
	kaleidoscope_head_init_perm(&perm.kt_kh, kaleid_test_add,
				    kaleid_test_remove, kaleid_test_free);
	printf("perm: ");
	dump_kaleid_test(&perm);
	BUG_ON(!kaleidoscope_exists(&perm.kt_kh));
	BUG_ON(!kaleidoscope_exists_relaxed(&perm.kt_kh));

	for (i = 0; i < KALEID_N_STATES; i++) {
		kaleid_test_init(&states[i]);
		ret = kaleidoscope_head_init_state(&states[i].kt_kh, &kg, i,
						   kaleid_test_add,
						   kaleid_test_remove,
						   kaleid_test_free);
		printf("State %d (%d): ", i, ret);
		dump_kaleid_test(&states[i]);
		BUG_ON(kaleidoscope_exists(&states[i].kt_kh) != (i == 0));
		BUG_ON(kaleidoscope_exists_relaxed(&states[i].kt_kh) !=
						   (i == 0));
	}
}

int main(int argc, char *argv[])
{
	int i;
	int j;

	setup();
	for (i = 0; i < KALEID_N_STATES; i++) {
		printf("Kaleidoscope state set to %d\n", i);
		kaleidoscope_set_state(&kg, i);
		BUG_ON(!kaleidoscope_exists(&perm.kt_kh));
		for (j = 0; j < KALEID_N_STATES; j++)
			BUG_ON(!!kaleidoscope_exists(&states[j].kt_kh) !=
			       (j == i));
	}
	synchronize_rcu();
	synchronize_rcu();
	dump_all();

	printf("\n");
	setup();
	printf("Kaleidoscope commit to state 0\n");
	kaleidoscope_set_state(&kg, 0);
	kaleidoscope_commit(&kg);
	BUG_ON(!kaleidoscope_exists(&perm.kt_kh));
	BUG_ON(!kaleidoscope_exists(&states[0].kt_kh));
	for (i = 1; i < KALEID_N_STATES; i++)
		BUG_ON(kaleidoscope_exists(&states[i].kt_kh) != (i == 0));
	synchronize_rcu();
	synchronize_rcu();
	dump_all();

	return 0;
}
