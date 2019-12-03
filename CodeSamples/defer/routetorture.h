/*
 * routetorture.h: simple user-level stress test of route tables.
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

#define _GNU_SOURCE
#include <unistd.h>
#include <stdlib.h>
#include <stdarg.h>
#include <sched.h>
#include <string.h>
#include "../lib/random.h"

#ifndef route_register_thread
#define route_register_thread() do { } while (0)
#endif /* #ifndef route_register_thread */

#ifndef quiescent_state
#define quiescent_state() do ; while (0)
#define synchronize_rcu() do ; while (0)
#endif /* #ifndef quiescent_state */

#ifndef other_init
#define other_init() do { } while (0)
#endif /* #ifndef other_init */

void smoketest(void)
{
	int i;

	route_register_thread();

	for (i = 0; i < 8; i++)
		BUG_ON(route_lookup(i) != ULONG_MAX);

	for (i = 0; i < 8; i++) {
		route_add(i, 2 * i);
		BUG_ON(route_lookup(i) != 2 * i);
	}

	for (i = 0; i < 8; i++) {
		route_del(i);
		BUG_ON(route_lookup(i) != ULONG_MAX);
	}

	route_unregister_thread();

	printf("End of smoketest.\n");
}

/* Parameters for performance test. */
int nelems = 100;
int nreaders = 7;
int nupdaters = 7;
int cpustride = 1;
long duration = 10; /* in milliseconds. */

atomic_t nthreads_running;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

/* Per-test-thread attribute/statistics structure. */
struct perftest_attr {
	int myid;
	long long nlookups;
	long long nlookupfails;
	long long nadds;
	long long ndels;
	long long ndelfails;
	int mycpu;
};

/* Performance test reader thread. */
void *perftest_reader(void *arg)
{
	long i;
	int gf;
	struct perftest_attr *pap = arg;
	long long nlookups = 0;
	long long nlookupfails = 0;

	run_on(pap->mycpu);
	route_register_thread();

	/* Announce our presence and enter the test loop. */
	atomic_inc(&nthreads_running);
	for (;;) {
		gf = READ_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nlookups = 0;
				nlookupfails = 0;
			}
		}
		i = random() % nelems;
		nlookups++;
		if (route_lookup(i) == ULONG_MAX) {
			nlookupfails++;
		}
	}

	/* Really want rcu_barrier(), but missing from old liburcu versions. */
	synchronize_rcu();
	poll(NULL, 0, 100);
	synchronize_rcu();

	route_unregister_thread();
	pap->nlookups = nlookups;
	pap->nlookupfails = nlookupfails;
	return NULL;
}

/* Run a stress test. */
void perftest(void)
{
	struct perftest_attr *pap;
	int maxcpus = sysconf(_SC_NPROCESSORS_CONF);
	long i;
	long long nlookups = 0;
	long long nlookupfails = 0;
	long long nadds = 0;
	long long ndels = 0;
	long long ndelfails = 0;
	long long starttime;

	BUG_ON(maxcpus <= 0);
	pap = malloc(sizeof(*pap) * nreaders);
	BUG_ON(pap == NULL);
	atomic_set(&nthreads_running, 0);
	WRITE_ONCE(goflag, GOFLAG_INIT);

	/* Populate route table. */
	for (i = 0; i < nelems; i++)
		route_add(i, 2 * i);

	for (i = 0; i < nreaders; i++) {
		pap[i].myid = i;
		pap[i].nlookups = 0;
		pap[i].nlookupfails = 0;
		pap[i].nadds = 0;
		pap[i].ndels = 0;
		pap[i].ndelfails = 0;
		pap[i].mycpu = (i * cpustride) % maxcpus;
		create_thread(perftest_reader, &pap[i]);
	}

	/* Wait for all threads to initialize. */
	while (atomic_read(&nthreads_running) < nreaders)
		poll(NULL, 0, 1);
	smp_mb();

	/* Run the test. */
	starttime = get_microseconds();
	WRITE_ONCE(goflag, GOFLAG_RUN);
	poll(NULL, 0, duration);
	WRITE_ONCE(goflag, GOFLAG_STOP);
	starttime = get_microseconds() - starttime;
	wait_all_threads();

	/* Collect stats and output them. */
	for (i = 0; i < nreaders; i++) {
		nlookups += pap[i].nlookups;
		nlookupfails += pap[i].nlookupfails;
		nadds += pap[i].nadds;
		ndels += pap[i].ndels;
		ndels += pap[i].ndelfails;
	}
	printf("nlookups: %lld %lld  nadds: %lld  ndels: %lld %lld  duration: %g\n",
	       nlookups, nlookupfails, nadds, ndels, ndelfails, starttime / 1000.);
	printf("ns/read: %g  ns/update: %g\n",
	       (starttime * 1000. * (double)nreaders) / (double)nlookups,
	       ((starttime * 1000. * (double)nreaders) /
	        (double)(nadds + ndels)));

	free(pap);
}

/* Stress test updater thread. */
void *stresstest_updater(void *arg)
{
	long i;
	long j;
	int gf;
	struct perftest_attr *pap = arg;
	unsigned long nids = nupdaters * 3;
	long long nlookups = 0;
	long long nlookupfails = 0;
	long long nadds = 0;
	long long ndels = 0;
	long long ndelfails = 0;

	run_on(pap->mycpu);
	route_register_thread();

	/* Start with some random half of the elements in the route table. */
	for (i = 0; i < nupdaters; i++) {
		j = random() % nids;
		route_add(j, 2 * j);
		j = random() % nids;
		route_del(j);
	}

	/* Announce our presence and enter the test loop. */
	atomic_inc(&nthreads_running);
	for (;;) {
		gf = READ_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nlookups = 0;
				nlookupfails = 0;
				nadds = 0;
				ndels = 0;
				ndelfails = 0;
			}
		}
		i = random() % nids;
		nlookups++;
		if (route_lookup(i) == ULONG_MAX) {
			nlookupfails++;
			route_add(i, 2 * i);
			nadds++;
		}
		i = random() % nids;
		ndels++;
		if (route_del(i) == -ENOENT)
			ndelfails++;
	}

	/* Test over, so remove all our elements from the route table. */
	for (i = 0; i < nids; i++) {
		route_del(i);
	}
	/* Really want rcu_barrier(), but missing from old liburcu versions. */
	synchronize_rcu();
	poll(NULL, 0, 100);
	synchronize_rcu();

	route_unregister_thread();
	pap->nlookups = nlookups;
	pap->nlookupfails = nlookupfails;
	pap->nadds = nadds;
	pap->ndels = ndels;
	pap->ndelfails = ndelfails;
	return NULL;
}

/* Run a stress test. */
void stresstest(void)
{
	struct perftest_attr *pap;
	int maxcpus = sysconf(_SC_NPROCESSORS_CONF);
	long i;
	long long nlookups = 0;
	long long nlookupfails = 0;
	long long nadds = 0;
	long long ndels = 0;
	long long ndelfails = 0;
	long long starttime;

	BUG_ON(maxcpus <= 0);
	pap = malloc(sizeof(*pap) * nupdaters);
	BUG_ON(pap == NULL);
	atomic_set(&nthreads_running, 0);
	WRITE_ONCE(goflag, GOFLAG_INIT);

	for (i = 0; i < nupdaters; i++) {
		pap[i].myid = i;
		pap[i].nlookups = 0;
		pap[i].nlookupfails = 0;
		pap[i].nadds = 0;
		pap[i].ndels = 0;
		pap[i].ndelfails = 0;
		pap[i].mycpu = (i * cpustride) % maxcpus;
		create_thread(stresstest_updater, &pap[i]);
	}

	/* Wait for all threads to initialize. */
	while (atomic_read(&nthreads_running) < nupdaters)
		poll(NULL, 0, 1);
	smp_mb();

	/* Run the test. */
	starttime = get_microseconds();
	WRITE_ONCE(goflag, GOFLAG_RUN);
	poll(NULL, 0, duration);
	WRITE_ONCE(goflag, GOFLAG_STOP);
	starttime = get_microseconds() - starttime;
	wait_all_threads();

	/* Collect stats and output them. */
	for (i = 0; i < nupdaters; i++) {
		nlookups += pap[i].nlookups;
		nlookupfails += pap[i].nlookupfails;
		nadds += pap[i].nadds;
		ndels += pap[i].ndels;
		ndels += pap[i].ndelfails;
	}
	printf("nlookups: %lld %lld  nadds: %lld  ndels: %lld %lld  duration: %g\n",
	       nlookups, nlookupfails, nadds, ndels, ndelfails, starttime / 1000.);
	printf("ns/read: %g  ns/update: %g\n",
	       (starttime * 1000. * (double)nupdaters) / (double)nlookups,
	       ((starttime * 1000. * (double)nupdaters) /
	        (double)(nadds + ndels)));

	free(pap);
}

/* Common argument-parsing code. */

void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "Usage: %s --perftest\n", progname);
	fprintf(stderr, "Usage: %s --smoketest\n", progname);
	fprintf(stderr, "Usage: %s --stresstest\n", progname);
	fprintf(stderr, "\t--nelems\n");
	fprintf(stderr, "\t\tNumber of elements, defaults to 100.  Must be\n");
	fprintf(stderr, "\t\t1 or greater.\n");
	fprintf(stderr, "\t--nreaders\n");
	fprintf(stderr, "\t\tNumber of readers, defaults to 7.  Must be 1\n");
	fprintf(stderr, "\t\tor greater.\n");
	fprintf(stderr, "\t--nupdaters\n");
	fprintf(stderr, "\t\tNumber of updaters, defaults to 7.  Must be 1\n");
	fprintf(stderr, "\t\tor greater.\n");
	fprintf(stderr, "\t--cpustride\n");
	fprintf(stderr, "\t\tStride when spreading threads across CPUs,\n");
	fprintf(stderr, "\t\tdefaults to 1.\n");
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds.\n");
	exit(EXIT_FAILURE);
}

/*
 * Mainprogram.
 */
int main(int argc, char *argv[])
{
	int i = 1;
	void (*test_to_do)(void) = NULL;

	smp_init();
	other_init();

	while (i < argc) {
		if (strcmp(argv[i], "--smoketest") == 0) {
			if (i < argc - 1 || i != 1)
				usage(argv[0],
				      "Excess arguments for %s\n", argv[i]);
			smoketest();
			exit(EXIT_SUCCESS);
		} else if (strcmp(argv[i], "--perftest") == 0) {
			test_to_do = perftest;
			if (i != 1)
				usage(argv[0],
				      "Must be first argument: %s\n", argv[i]);
		} else if (strcmp(argv[i], "--stresstest") == 0) {
			test_to_do = stresstest;
			if (i != 1)
				usage(argv[0],
				      "Must be first argument: %s\n", argv[i]);
		} else if (strcmp(argv[i], "--nelems") == 0) {
			nelems = strtol(argv[++i], NULL, 0);
			if (nupdaters < 1)
				usage(argv[0],
				      "%s must be >= 1\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nreaders") == 0) {
			nreaders = strtol(argv[++i], NULL, 0);
			if (nupdaters < 1)
				usage(argv[0],
				      "%s must be >= 1\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nupdaters") == 0) {
			nupdaters = strtol(argv[++i], NULL, 0);
			if (nupdaters < 1)
				usage(argv[0],
				      "%s must be >= 1\n", argv[i - 1]);
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
	if (!test_to_do)
		usage(argv[0], "No test specified\n");
	test_to_do();
	return 0;
}
