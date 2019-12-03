/*
 * existence_test.c: Test existence data structures.
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
#include "existence.h"

struct exist_test {
	struct existence_head et_eh;
	int et_added;
	int et_removed;
	int et_freed;
};

struct existence_group eg;

struct exist_test incoming;
struct exist_test outgoing;
struct exist_test perm;

static void exist_test_init(struct exist_test *etp)
{
	etp->et_added = 0;
	etp->et_removed = 0;
	etp->et_freed = 0;
}

static int exist_test_add(struct existence_head *ehp)
{
	struct exist_test *etp = container_of(ehp, struct exist_test, et_eh);

	etp->et_added = 1;
	return 0;
}

static void exist_test_remove(struct existence_head *ehp)
{
	struct exist_test *etp = container_of(ehp, struct exist_test, et_eh);

	etp->et_removed = 1;
}

static void exist_test_free(struct existence_head *ehp)
{
	struct exist_test *etp = container_of(ehp, struct exist_test, et_eh);

	etp->et_freed = 1;
}

static void dump_existence_group(struct existence_group *egp)
{
	struct existence_head *ehp;

	printf("Existence group %p  state: %lu\n",  egp, egp->eg_state);
	printf("\tIncoming:");
	cds_list_for_each_entry(ehp, &egp->eg_incoming, eh_list)
		printf(" %p", ehp);
	printf("\n");
	printf("\tOutgoing:");
	cds_list_for_each_entry(ehp, &egp->eg_outgoing, eh_list)
		printf(" %p", ehp);
	printf("\n");
}

static void dump_existence_head(struct existence_head *ehp)
{
	printf("Existence head %p egi: %#lx  %c%c add: %p remove: %p free: %p\n",
	       ehp, ehp->eh_egi,
	       "L."[!!cds_list_empty(&ehp->eh_list)],
	       ".G"[!!ehp->eh_gone],
	       ehp->eh_add, ehp->eh_remove, ehp->eh_free);
}

static void dump_exist_test(struct exist_test *etp)
{
	dump_existence_head(&etp->et_eh);
	printf("\t%s %s %s\n",
	       etp->et_added ? "added" : "unadded",
	       etp->et_removed ? "removed" : "unremoved",
	       etp->et_freed ? "freed" : "unfreed");
}

static void dump_all(void)
{
	dump_existence_group(&eg);
	printf("perm: ");
	dump_exist_test(&perm);
	printf("incoming: ");
	dump_exist_test(&incoming);
	printf("outgoing: ");
	dump_exist_test(&outgoing);
}

void setup(void)
{
	int ret;

	existence_group_init(&eg);
	dump_existence_group(&eg);

	exist_test_init(&perm);
	existence_head_init_perm(&perm.et_eh, exist_test_add, exist_test_remove,
				 exist_test_free);
	printf("perm: ");
	dump_exist_test(&perm);
	BUG_ON(!existence_exists(&perm.et_eh));
	BUG_ON(!existence_exists_relaxed(&perm.et_eh));

	exist_test_init(&incoming);
	ret = existence_head_init_incoming(&incoming.et_eh, &eg, exist_test_add,
					   exist_test_remove, exist_test_free);
	printf("incoming (%d): ", ret);
	dump_exist_test(&incoming);
	BUG_ON(existence_exists(&incoming.et_eh));
	BUG_ON(existence_exists_relaxed(&incoming.et_eh));

	exist_test_init(&outgoing);
	existence_head_init_perm(&outgoing.et_eh, exist_test_add,
				 exist_test_remove, exist_test_free);
	printf("not yet outgoing: ");
	dump_exist_test(&outgoing);
	ret = existence_head_set_outgoing(&outgoing.et_eh, &eg);
	printf("outgoing (%d): ", ret);
	dump_exist_test(&outgoing);
	BUG_ON(!existence_exists(&outgoing.et_eh));
	BUG_ON(!existence_exists_relaxed(&outgoing.et_eh));
}

int main(int argc, char *argv[])
{
	setup();
	printf("Existence flip\n");
	existence_flip(&eg);
	BUG_ON(!existence_exists(&perm.et_eh));
	BUG_ON(!existence_exists(&incoming.et_eh));
	BUG_ON(existence_exists(&outgoing.et_eh));
	synchronize_rcu();
	synchronize_rcu();
	dump_all();

	printf("\n");
	setup();
	printf("Existence backout\n");
	existence_backout(&eg);
	BUG_ON(!existence_exists(&perm.et_eh));
	BUG_ON(existence_exists(&incoming.et_eh));
	BUG_ON(!existence_exists(&outgoing.et_eh));
	synchronize_rcu();
	synchronize_rcu();
	dump_all();

	return 0;
}
