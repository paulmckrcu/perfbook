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

#include <jemalloc/jemalloc.h>
#include "stdarg.h"
#include <string.h>
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

#include "procon.h"
#include "keyvalue.h"
#include "hash_exists.h"

/* Parameters for performance test. */
int nbuckets = 4096;
int nreaders = 0;
int nupdaters = 1;
int updatewait = -1;
long updatespacing = 32;
int cpustride = 1;
long duration = 10; /* in milliseconds. */

atomic_t nthreads_running;
atomic_t nthreads_done;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

struct hashtab *ht_array[3];

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
};

/*
 * Rotate values through the three hash tables, shifting in the key
 * specified by nextkey.
 */
void hash_rotate(struct hashtab *htp[],
		 struct hash_exists *hei[], struct hash_exists *heo[])
{
	struct existence_group *egp;

	egp = malloc(sizeof(*egp));
	BUG_ON(!egp);
	existence_group_init(egp);
	rcu_read_lock();
	heo[0] = hash_exists_alloc(egp, htp[0], hei[2]->he_kv, ~0, ~0);
	heo[1] = hash_exists_alloc(egp, htp[1], hei[0]->he_kv, ~0, ~0);
	heo[2] = hash_exists_alloc(egp, htp[2], hei[1]->he_kv, ~0, ~0);
	BUG_ON(existence_head_set_outgoing(&hei[0]->he_eh, egp));
	BUG_ON(existence_head_set_outgoing(&hei[1]->he_eh, egp));
	BUG_ON(existence_head_set_outgoing(&hei[2]->he_eh, egp));
	rcu_read_unlock();
	existence_flip(egp);
	call_rcu(&egp->eg_rh, existence_group_rcu_cb);
#if 0
	if (atomic_read(&heo[0]->he_kv->refcnt) > 10000)
		poll(NULL, 0, 1);
#endif
}

void *perftest_child(void *arg)
{
	struct perftest_attr *childp = arg;
	struct call_rcu_data *crdp;
	struct existence_group *egp;
	struct hash_exists *hei[3];
	struct hash_exists *heo[3];
	int i;
	long long nrotations = 0LL;

	rcu_register_thread();
	run_on(childp->mycpu);
	crdp = create_call_rcu_data(0, childp->mycpu);
	set_thread_call_rcu_data(crdp);
	keyvalue__procon_init();
	hash_exists__procon_init();
	atomic_inc(&nthreads_running);
	egp = malloc(sizeof(*egp));
	BUG_ON(!egp);
	existence_group_init(egp);
	rcu_read_lock();
	for (i = 0; i < 3; i++)
		hei[i] = hash_exists_alloc(egp, ht_array[i], NULL,
					   childp->firstkey + i,
					   childp->firstkey + i);
	rcu_read_unlock();
	existence_flip(egp);
	call_rcu(&egp->eg_rh, existence_group_rcu_cb);
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		hash_rotate(ht_array, hei, heo);
		for (i = 0; i < 3; i++)
			hei[i] = heo[i];
		nrotations++;
	}
	rcu_unregister_thread();
	childp->nrotations = nrotations;
	rcu_barrier();
	atomic_inc(&nthreads_done);
	set_thread_call_rcu_data(NULL);
	call_rcu_data_free(crdp);
	return NULL;
}


void perftest(void)
{
	struct perftest_attr *childp = malloc(sizeof(*childp) * nupdaters);
	int i;
	long long nrotations = 0LL;
	long long starttime;
	long long endtime;

	rcu_read_lock();
	for (i = 0; i < 3; i++) {
		ht_array[i] = hashtab_alloc(nbuckets, hash_exists_cmp);
		BUG_ON(!ht_array[i]);
	}
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

	for (i = 0; i < nupdaters; i++) {
		nrotations += childp[i].nrotations;
	}
	printf("rotations: %lld  ns/rotation: %g\n", nrotations,
	       (starttime * 1000. * (double)nupdaters) / (double)nrotations);
	free(childp);
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
	fprintf(stderr, "\t\tdefaults to 32.  Must be greater than zero.\n");
	fprintf(stderr, "\t--cpustride\n");
	fprintf(stderr, "\t\tStride when spreading threads across CPUs,\n");
	fprintf(stderr, "\t\tdefaults to 1.\n");
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds.\n");
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
			if (updatespacing < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--cpustride") == 0) {
			cpustride = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = strtol(argv[++i], NULL, 0);
			if (duration < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else {
			usage(argv[0], "Unrecognized argument: %s\n",
			      argv[i]);
		}
		i++;
	}
	test_to_do();
	return 0;
}
