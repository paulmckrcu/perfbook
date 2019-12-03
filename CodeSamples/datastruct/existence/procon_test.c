/*
 * procon_test.c: Test existence data structures.
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

struct mystruct {
	int a;
	struct procon_mblock pm;
	struct rcu_head rh;
};

DEFINE_PROCON_MPOOL(mystruct, pm, calloc(1, sizeof(struct mystruct)))

void mystruct_rcu_cb(struct rcu_head *rhp)
{
	struct mystruct *msp;

	msp = container_of(rhp, struct mystruct, rh);
	BUG_ON(!msp->a);
	msp->a = 0;
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
	rcu_barrier();
	for (i = 0; i < 100 * 1000 * 1000; i++) {
		msp = mystruct__procon_alloc();
		BUG_ON(!msp);
		BUG_ON(msp->a);
		msp->a = 1;
		if (i & 0x1) {
			call_rcu(&msp->rh, mystruct_rcu_cb);
		} else {
			msp->a = 0;
			mystruct__procon_unalloc(msp);
		}
	}
	printf("mystruct__procon_mpool: alloc: %lu out: %lu in: %lu unout: %lu\n",
	       mystruct__procon_mpool->pm_alloccount,
	       mystruct__procon_mpool->pm_outcount,
	       mystruct__procon_mpool->pm_incount,
	       mystruct__procon_mpool->pm_unoutcount);

	synchronize_rcu();
	poll(NULL, 0, 10);
	synchronize_rcu();

	printf("mystruct__procon_mpool: alloc: %lu out: %lu in: %lu unout: %lu\n",
	       mystruct__procon_mpool->pm_alloccount,
	       mystruct__procon_mpool->pm_outcount,
	       mystruct__procon_mpool->pm_incount,
	       mystruct__procon_mpool->pm_unoutcount);

	return 0;
}
