/*
 * kaleidoscope_skiphash_test.c: Test kaleidoscopic data structures for a
 *	skiplist and a hash table.
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

#include "stdarg.h"
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
#include "../hash/hash_bkt_rcu.c"

#include "procon.h"
#include "kaleidoscope.h"
#include "keyvalue.h"
#include "hash_kaleid.h"
#include "skiplist_kaleid.h"

struct skiplist sl_head;
struct hashtab *ht_head;

/* Parameters for performance test. */
int nbuckets = 4096;
int nobjects;
int nreaders = 0;
int nupdaters = 1;
int updatewait = -1;
long updatespacing = 32;
int cpustride = 1;
long duration = 10; /* in milliseconds. */
long dump_procon_stats = 0;

atomic_t nthreads_running;
atomic_t nthreads_done;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

/* Per-test-thread attribute/statistics structure. */
struct perftest_attr {
	int myid;
	long long nlookups;
	long long nlookupfails;
	long long nrotations;
	long long nadds;
	long long ndels;
	int mycpu;
	long firstkey;
	struct procon_stats kv_ps;
	struct procon_stats hk_ps;
	struct procon_stats sk_ps;
	struct procon_stats eg_ps;
};

void *perftest_child(void *arg)
{
	struct perftest_attr *childp = arg;
	struct call_rcu_data *crdp;
	struct kaleidoscope_group *kgp;
	struct hash_kaleid **hke;
	struct skiplist_kaleid **ske;
	int i;
	long long nrotations = 0LL;

	rcu_register_thread();
	run_on(childp->mycpu);
	crdp = create_call_rcu_data(URCU_CALL_RCU_RT, childp->mycpu);
	set_thread_call_rcu_data(crdp);
	keyvalue__procon_init();
	hash_kaleid__procon_init();
	skiplist_kaleid__procon_init();
	kaleidoscope_group__procon_init();
	atomic_inc(&nthreads_running);
	kgp = kaleidoscope_group__procon_alloc();
	BUG_ON(!kgp);
	kaleidoscope_group_init(kgp);
	hke = calloc(sizeof(*hke), 2 * nobjects);
	ske = calloc(sizeof(*ske), 2 * nobjects);
	rcu_read_lock();
	for (i = 0; i < 2 * nobjects; i++) {
		hke[i] = hash_kaleid_alloc(kgp, ht_head, NULL, i % 2,
					   childp->firstkey + i,
					   childp->firstkey + i);
		ske[i] = skiplist_kaleid_alloc(kgp, &sl_head, NULL, i % 2,
					       childp->firstkey + i,
					       childp->firstkey + i);
	}
	rcu_read_unlock();
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		kaleidoscope_set_state(kgp, nrotations % 2);
		nrotations++;
	}
	free(hke);
	free(ske);
	rcu_unregister_thread();
	childp->nrotations = nrotations;
	rcu_barrier();
	keyvalue__procon_stats(&childp->kv_ps);
	hash_kaleid__procon_stats(&childp->hk_ps);
	skiplist_kaleid__procon_stats(&childp->sk_ps);
	kaleidoscope_group__procon_stats(&childp->eg_ps);
	atomic_inc(&nthreads_done);
	set_thread_call_rcu_data(NULL);
	call_rcu_data_free(crdp);
	return NULL;
}


void perftest(void)
{
	struct perftest_attr *childp = calloc(sizeof(*childp), nupdaters);
	int i;
	long long nrotations = 0LL;
	long long starttime;
	long long endtime;
	struct procon_stats kv_pst = { 0 };
	struct procon_stats hk_pst = { 0 };
	struct procon_stats sk_pst = { 0 };
	struct procon_stats eg_pst = { 0 };

	rcu_register_thread();
	keyvalue__procon_init();
	hash_kaleid__procon_init();
	skiplist_kaleid__procon_init();
	kaleidoscope_group__procon_init();

	rcu_read_lock();
	ht_head = hashtab_alloc(nbuckets, hash_kaleid_cmp);
	skiplist_init(&sl_head, skiplist_kaleid_cmp);
	rcu_read_unlock();

	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nupdaters; i++) {
		childp[i].myid = i;
		childp[i].nlookups = 0LL;
		childp[i].nlookupfails = 0LL;
		childp[i].nrotations = 0LL;
		childp[i].nadds = 0LL;
		childp[i].ndels = 0LL;
		childp[i].mycpu = i * cpustride;
		childp[i].firstkey = i * updatespacing;
		create_thread(perftest_child, &childp[i]);
	}
	rcu_unregister_thread();

	/* Wait for all threads to initialize. */
	while (atomic_read(&nthreads_running) < nreaders + nupdaters)
		poll(NULL, 0, 1);
	smp_mb();

	/* Run the test. */
	starttime = get_microseconds();
	ACCESS_ONCE(goflag) = GOFLAG_RUN;
	do {
		poll(NULL, 0, duration);
		endtime = get_microseconds();
	} while (endtime - starttime < duration * 1000);
	starttime = endtime - starttime;
	ACCESS_ONCE(goflag) = GOFLAG_STOP;
	wait_all_threads();

	rcu_register_thread();
	for (i = 0; i < nupdaters; i++) {
		nrotations += childp[i].nrotations;
		procon_stats_accumulate(&kv_pst, &childp[i].kv_ps);
		procon_stats_accumulate(&hk_pst, &childp[i].hk_ps);
		procon_stats_accumulate(&sk_pst, &childp[i].sk_ps);
		procon_stats_accumulate(&eg_pst, &childp[i].eg_ps);
	}
	printf("duration (s): %g  rotations: %lld  ns/rotation: %g  obj/hash/thread: %d\n",
	       starttime / 1000. / 1000., nrotations,
	       (starttime * 1000. * (double)nupdaters) / (double)nrotations,
	       nobjects);
	if (dump_procon_stats) {
		printf("Key-value producer-consumer statistics:\n");
		procon_stats_print(&kv_pst);
		printf("Hash-kaleidoscope producer-consumer statistics:\n");
		procon_stats_print(&hk_pst);
		printf("Skiplist-kaleidoscope producer-consumer statistics:\n");
		procon_stats_print(&sk_pst);
		printf("Existence-group producer-consumer statistics:\n");
		procon_stats_print(&eg_pst);
	}
	free(childp);
	rcu_unregister_thread();
	rcu_barrier();
}

void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "\t--nbuckets\n");
	fprintf(stderr, "\t\tNumber of buckets, defaults to 4096.\n");
	fprintf(stderr, "\t--nupdaters\n");
	fprintf(stderr, "\t\tNumber of updaters, defaults to 1.  Must be 1\n");
	fprintf(stderr, "\t\tor greater, or hash table will be empty.\n");
	fprintf(stderr, "\t--updatewait\n");
	fprintf(stderr, "\t\tNumber of spin-loop passes per update,\n");
	fprintf(stderr, "\t\tdefaults to -1.  If 0, the updater will not.\n");
	fprintf(stderr, "\t\tdo any updates, except for initialization.\n");
	fprintf(stderr, "\t\tIf negative, the updater waits for the\n");
	fprintf(stderr, "\t\tcorresponding number of milliseconds\n");
	fprintf(stderr, "\t\tbetween updates.\n");
	fprintf(stderr, "\t--updatespacing\n");
	fprintf(stderr, "\t\tKey values between successive updaters,\n");
	fprintf(stderr, "\t\tdefaults to 32.  Must be greater than 19.\n");
	fprintf(stderr, "\t--cpustride\n");
	fprintf(stderr, "\t\tStride when spreading threads across CPUs,\n");
	fprintf(stderr, "\t\tdefaults to 1.\n");
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds.\n");
	fprintf(stderr, "\t--dump-procon-stats\n");
	fprintf(stderr, "\t\tDump procon memory-piping statistics.\n");
	hashtab_lock_lookup(NULL, 0);  /* Suppress unused warning. */
	hashtab_unlock_lookup(NULL, 0);
	exit(-1);
}

/*
 * Mainprogram.
 */
int main(int argc, char *argv[])
{
	int i = 1;
	void (*test_to_do)(void) = perftest;

	smp_init();

	while (i < argc) {
		if (strcmp(argv[i], "--nbuckets") == 0) {
			nbuckets = strtol(argv[++i], NULL, 0);
			if (nbuckets < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nreaders") == 0) {
			nreaders = strtol(argv[++i], NULL, 0);
			if (nreaders < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nupdaters") == 0) {
			nupdaters = strtol(argv[++i], NULL, 0);
			if (nupdaters < 1)
				usage(argv[0],
				      "%s must be >= 1\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--updatewait") == 0) {
			updatewait = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--updatespacing") == 0) {
			updatespacing = strtol(argv[++i], NULL, 0);
			if (updatespacing < 20)
				usage(argv[0],
				      "%s must be >= 32\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--cpustride") == 0) {
			cpustride = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = strtol(argv[++i], NULL, 0);
			if (duration < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--dump-procon-stats") == 0) {
			dump_procon_stats = 1;
		} else {
			usage(argv[0], "Unrecognized argument: %s\n",
			      argv[i]);
		}
		i++;
	}
	nobjects = (updatespacing - 16) / 3;
	test_to_do();
	return 0;
}
