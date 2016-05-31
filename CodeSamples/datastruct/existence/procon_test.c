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
#include "procon.h"

struct mystruct {
	int a;
	struct procon_mblock pm;
	struct rcu_head rh;
};

DEFINE_PROCON_MPOOL(mystruct, pm, malloc(sizeof(struct mystruct)))

void mystruct_rcu_cb(struct rcu_head *rhp)
{
	struct mystruct *msp;

	msp = container_of(rhp, struct mystruct, rh);
	mystruct__procon_free(msp);
}

int main(int argc, char *argv[])
{
	struct call_rcu_data *crdp;
	int i;
	struct mystruct *msp;

	rcu_register_thread();
	run_on(0);
	crdp = create_call_rcu_data(0, 0);
	set_thread_call_rcu_data(crdp);
	mystruct__procon_init();
	for (i = 0; i < 100 * 1000 * 1000; i++) {
		msp = mystruct__procon_alloc();
		BUG_ON(!msp);
		call_rcu(&msp->rh, mystruct_rcu_cb);
	}
	printf("mystruct__procon_mpool: alloc: %lu out: %lu in: %lu\n",
	       mystruct__procon_mpool.pm_alloccount,
	       mystruct__procon_mpool.pm_outcount,
	       mystruct__procon_mpool.pm_incount);

	poll(NULL, 0, 10);

	printf("mystruct__procon_mpool: alloc: %lu out: %lu in: %lu\n",
	       mystruct__procon_mpool.pm_alloccount,
	       mystruct__procon_mpool.pm_outcount,
	       mystruct__procon_mpool.pm_incount);

	return 0;
}
