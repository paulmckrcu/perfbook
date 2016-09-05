/*
 * logtorture.h: simple user-level performance/stress test of logging.
 *
 * Usage:
 *
 *	./log_glock --smoketest
 *		Run a simple single-threaded smoke test.
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

#define _GNU_SOURCE
#include <unistd.h>
#include <stdlib.h>
#include <stdarg.h>
#include <sched.h>
#include <string.h>

/*
 * Test variables.
 */

struct log_head test_log;

/*
 * Print one log entry.
 */
void log_print(struct log_head *lhp, long cur_idx)
{
	long max_idx = get_log_next_idx(lhp);

	if (cur_idx >= max_idx) {
		printf("No log records at index %ld\n", cur_idx);
		return;
	}
	printf("\t%ld: %lu\n", cur_idx, get_log_value(lhp, cur_idx));
}

/*
 * Dump the log starting at the specified index.
 */
void log_dump(struct log_head *lhp, long start_idx)
{
	long i;
	long max_idx = get_log_next_idx(lhp);

	if (start_idx < 0)
		i = max_idx + start_idx;
	else
		i = start_idx;
	if (i < 0)
		i = 0;
	if (i >= max_idx) {
		printf("No log records past index %ld (%ld)\n", i, start_idx);
		return;
	}
	printf("Log %p starting at %ld (%ld):\n", lhp, i, start_idx);
	for (; i < max_idx; i++)
		log_print(lhp, i);
}

void add_one_log_record(struct log_head *lhp, unsigned long val, long stidx)
{
	long idx;
	long idx1;

	printf("\n");
	printf("Add entry: %ld\n", val);
	idx = log_append(&test_log, val);
	idx1 = get_log_next_idx(&test_log);
	if (idx1 != idx + 1)
		abort();
	printf("Log next_idx from append: %ld, sampled: %ld, dump\n",
	       idx, idx1);
	log_dump(&test_log, stidx);
}

void smoketest(void)
{
	log_init(&test_log, 16);

	printf("Initial empty log next_idx: %ld\n",
	       get_log_next_idx(&test_log));
	if (get_log_next_idx(&test_log) != 0)
		abort();
	printf("Initial empty log:\n");
	log_dump(&test_log, 0);
	printf("Initial empty log, starting from (nonexistent) entry 1:\n");
	log_dump(&test_log, 1);

	add_one_log_record(&test_log, 42UL, 0);
	printf("Dump more than all the log\n");
	log_dump(&test_log, -10);

	add_one_log_record(&test_log, 43UL, 0);
	printf("Dump last entry of log\n");
	log_dump(&test_log, -1);

	add_one_log_record(&test_log, 44UL, 0);
	printf("Dump last two entries of log\n");
	log_dump(&test_log, -2);

	log_cleanup(&test_log);
	printf("End of smoketest.\n");
}

/* Parameters for performance test. */
int dump_skiplists = 0;
int no_bal = 0;
int no_scan = 0;
int nreaders = 2;
int nupdaters = 5;
int updatewait = 1;
long elperupdater = 2048; /* Allow for them being stuck in grace periods. */
long valsperupdater = 32;
int cpustride = 1;
long duration = 10; /* in milliseconds. */
static int debug = 0;

#if 0 /* @@@ */

atomic_t nthreads_running;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

/* Per-test-thread attribute/statistics structure. */
struct stresstest_attr {
	int myid;
	long long nlookups;
	long long nlookupfails;
	long long nscans;
	long long nadds;
	long long naddfails;
	long long nbals;
	long long ndels;
	long long ndelfails;
	int mycpu;
	long nelements;
	int cat;
};

void (*defer_del_done)(struct testsl *) = NULL;

void defer_del_rcu(struct rcu_head *rhp)
{
	struct testsl *tslp;

	tslp = container_of(rhp, struct testsl, rh);
	defer_del_done(tslp);
}

struct testsl head_sl;

/* Look up a key in the skiplist. */
int stresstest_lookup(long i)
{
	struct skiplist *slp;
	struct testsl *tslp;

	slp = skiplist_lookup_relaxed(&head_sl.sle_e, (void *)i);
	tslp = container_of(slp, struct testsl, sle_e);
	BUG_ON(slp && tslp->data != i);
	BUG_ON(slp && !tslp->in_table);
	return !!slp;
}

/* Add an element to the skiplist. */
int stresstest_add(struct testsl *tslp)
{
	int result;

	BUG_ON(tslp->in_table);
	tslp->in_table = 1;
	result = skiplist_insert(&tslp->sle_e, &head_sl.sle_e,
				 (void *)tslp->data);
	if (result)
		tslp->in_table = 0;
	return result;
}

/* Remove an element from the skiplist. */
int stresstest_del(unsigned long key)
{
	struct skiplist *slp;
	struct testsl *tslp;

	slp = skiplist_delete(&head_sl.sle_e, (void *)key);
	if (!slp)
		return -ENOENT;
	tslp = container_of(slp, struct testsl, sle_e);
	tslp->in_table = 2;
	defer_del(&tslp->rh);
	return 0;
}

/* Do a forward and a reverse scan of the entire skiplist. */
int stresstest_reader_scan(void)
{
	struct skiplist_iter sli;
	struct skiplist *slp;
	struct testsl *tslp;

	/* Value-based iterators. */
	rcu_read_lock();
	slp = skiplist_valiter_first(&head_sl.sle_e);
	while (slp) {
		rcu_read_unlock();
		tslp = container_of(slp, struct testsl, sle_e);
		slp = skiplist_valiter_next(&head_sl.sle_e,
					    (void *)tslp->data);
		rcu_read_lock();
	}
	slp = skiplist_valiter_last(&head_sl.sle_e);
	while (slp) {
		rcu_read_unlock();
		tslp = container_of(slp, struct testsl, sle_e);
		slp = skiplist_valiter_prev(&head_sl.sle_e,
					    (void *)tslp->data);
		rcu_read_lock();
	}
	rcu_read_unlock();

	/* Pointer-hint-based iterators. */
	rcu_read_lock();
	slp = skiplist_ptriter_first(&head_sl.sle_e, &sli);
	while (slp) {
		rcu_read_unlock();
		tslp = container_of(slp, struct testsl, sle_e);
		slp = skiplist_ptriter_next(&head_sl.sle_e,
					    (void *)tslp->data, &sli);
		rcu_read_lock();
	}
	slp = skiplist_ptriter_last(&head_sl.sle_e, &sli);
	while (slp) {
		rcu_read_unlock();
		tslp = container_of(slp, struct testsl, sle_e);
		slp = skiplist_ptriter_prev(&head_sl.sle_e,
					    (void *)tslp->data, &sli);
		rcu_read_lock();
	}
	rcu_read_unlock();

	return 4;
}

/* Stress test reader thread. */
void *stresstest_reader(void *arg)
{
	int gf;
	long i;
	struct stresstest_attr *pap = arg;
	long long nlookups = 0;
	long long nlookupfails = 0;
	long long nscans = 0;

	run_on(pap->mycpu);
	rcu_register_thread();

	/* Warm up cache. */
	for (i = 0; i < valsperupdater * nupdaters; i++) {
		stresstest_lookup(i);
	}

	/* Record our presence. */
	atomic_inc(&nthreads_running);

	/* Run the test code. */
	i = 0;
	for (;;) {
		gf = ACCESS_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nlookups = 0;
				nlookupfails = 0;
				nscans = 0;
			}
		}
		rcu_read_lock();
		if (!stresstest_lookup(i))
			nlookupfails++;
		rcu_read_unlock();
		nlookups++;
		i++;
		if (i >= valsperupdater * nupdaters)
			i = 0;
		if (!no_scan)
			nscans += stresstest_reader_scan();
	}
	pap->nlookups = nlookups;
	pap->nlookupfails = nlookupfails;
	pap->nscans = nscans;
	rcu_unregister_thread();
	return NULL;
}

/* Stress test updater thread. */
void *stresstest_updater(void *arg)
{
	long i;
	long j;
	long k;
	void *key;
	int gf;
	struct stresstest_attr *pap = arg;
	int myid = pap->myid;
	int mylowkey = myid * elperupdater;
	struct testsl *tslp;
	long long nadds = 0;
	long long naddfails = 0;
	long long nbals = 0;
	long long ndels = 0;
	long long ndelfails = 0;

	tslp = malloc(sizeof(*tslp) * elperupdater);
	BUG_ON(tslp == NULL);
	for (i = 0; i < elperupdater; i++) {
		tslp[i].data = i % valsperupdater + mylowkey;
		tslp[i].in_table = 0;
	}
	run_on(pap->mycpu);
	rcu_register_thread();

	/* Start with some random half of the elements in the hash table. */
	for (i = 0; i < elperupdater / 2; i++) {
		j = random() % elperupdater;
		while (tslp[j].in_table)
			if (++j >= elperupdater)
				j = 0;
		stresstest_add(&tslp[j]);
	}

	/* Announce our presence and enter the test loop. */
	atomic_inc(&nthreads_running);
	i = 0;
	j = 0;
	for (;;) {
		gf = ACCESS_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nadds = 0;
				naddfails = 0;
				nbals = 0;
				ndels = 0;
				ndelfails = 0;
			}
		}
		if (updatewait == 0) {
			poll(NULL, 0, 10);  /* No actual updating wanted. */
		} else {
			while (tslp[i].in_table) {
				if (++i >= elperupdater) {
					i = 0;
					break;
				}
			}
			if (tslp[i].in_table == 0) {
				nadds++;
				if (stresstest_add(&tslp[i]))
					naddfails++;
				if ((nadds & 0xff) == 0)
					quiescent_state();
				if ((nadds & 0xff) == 0 && !no_bal) {
					k = random() % SL_MAX_LEVELS;
					key = (void *)tslp[i].data;
					skiplist_balance_node(&head_sl.sle_e,
							      key, k);
					nbals++;
				}
			}
			ndels++;
			if (stresstest_del((unsigned long)j))
				ndelfails++;
			if (++j >= valsperupdater * nupdaters)
				j = 0;
		}

		/* Add requested delay. */
		if (updatewait < 0) {
			poll(NULL, 0, -updatewait);
		} else {
			for (k = 0; k < updatewait; k++)
				barrier();
		}
	}

	/* Test over, so remove all our elements from the hash table. */
	for (i = 0; i < elperupdater; i++) {
		if (tslp[i].in_table != 1)
			continue;
		(void)stresstest_del(tslp[i].data);
	}

	skiplist_lock(&head_sl.sle_e);
	if (dump_skiplists) {
		printf("Skiplist dump 2 from thread %d\n:", pap->myid);
		sl_dump(&head_sl.sle_e);
		fflush(stdout);
	}
	skiplist_fsck(&head_sl.sle_e);
	skiplist_unlock(&head_sl.sle_e);

	/* Really want rcu_barrier(), but missing from old liburcu versions. */
	synchronize_rcu();
	poll(NULL, 0, 100);
	synchronize_rcu();

	skiplist_lock(&head_sl.sle_e);
	if (dump_skiplists) {
		printf("Skiplist dump 2 from thread %d\n:", pap->myid);
		sl_dump(&head_sl.sle_e);
		fflush(stdout);
	}
	skiplist_fsck(&head_sl.sle_e);
	skiplist_unlock(&head_sl.sle_e);

	rcu_unregister_thread();
	free(tslp);
	pap->nadds = nadds;
	pap->naddfails = naddfails;
	pap->nbals = nbals;
	pap->ndels = ndels;
	pap->ndelfails = ndelfails;
	return NULL;
}

/* Run a performance test. */
void stresstest(void)
{
	struct stresstest_attr *pap;
	int maxcpus = sysconf(_SC_NPROCESSORS_CONF);
	long i;
	long long nlookups = 0;
	long long nlookupfails = 0;
	long long nscans = 0;
	long long nadds = 0;
	long long naddfails = 0;
	long long nbals = 0;
	long long ndels = 0;
	long long ndelfails = 0;
	long long starttime;
	long long endtime;

	BUG_ON(maxcpus <= 0);
	rcu_register_thread();
	skiplist_init(&head_sl.sle_e, testcmp);
	defer_del_done = defer_del_done_stresstest;
	pap = malloc(sizeof(*pap) * (nreaders + nupdaters));
	BUG_ON(pap == NULL);
	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nreaders + nupdaters; i++) {
		pap[i].myid = i < nreaders ? i : i - nreaders;
		pap[i].nlookups = 0;
		pap[i].nlookupfails = 0;
		pap[i].nscans = 0;
		pap[i].nadds = 0;
		pap[i].naddfails = 0;
		pap[i].nbals = 0;
		pap[i].ndels = 0;
		pap[i].ndelfails = 0;
		pap[i].mycpu = (i * cpustride) % maxcpus;
		pap[i].nelements = nupdaters * elperupdater;
		create_thread(i < nreaders
					? stresstest_reader
					: stresstest_updater,
			      &pap[i]);
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

	/* Don't need to lock anything here: No more updates happening. */
	if (dump_skiplists) {
		printf("Skiplist dump from parent thread\n:");
		sl_dump(&head_sl.sle_e);
		fflush(stdout);
	}
	skiplist_fsck(&head_sl.sle_e);

	/* Collect stats and output them. */
	for (i = 0; i < nreaders + nupdaters; i++) {
		nlookups += pap[i].nlookups;
		nlookupfails += pap[i].nlookupfails;
		nscans += pap[i].nscans;
		nadds += pap[i].nadds;
		naddfails += pap[i].naddfails;
		nbals += pap[i].nbals;
		ndels += pap[i].ndels;
		ndelfails += pap[i].ndelfails;
	}
	printf("nlookups: %lld %lld scans: %lld  nadds: %lld %lld  nbals: %lld  ndels: %lld %lld  duration: %g\n",
	       nlookups, nlookupfails, nscans, nadds, naddfails, nbals, ndels, ndelfails, starttime / 1000.);
	printf("ns/read+scan: %g  ns/update: %g\n",
	       (starttime * 1000. * (double)nreaders) / (double)(nlookups + nscans),
	       ((starttime * 1000. * (double)nupdaters) /
	        (double)(nadds + ndels)));

	free(pap);
	rcu_unregister_thread();
}

#endif /* @@@ */

/* Common argument-parsing code. */
void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "Usage: %s --smoketest\n", progname);
	fprintf(stderr, "Usage: %s --stresstest\n", progname);
	fprintf(stderr, "\t--cpustride\n");
	fprintf(stderr, "\t\tCPU stride, defaults to 1.\n");
	fprintf(stderr, "\t--debug\n");
	fprintf(stderr, "\t\tEnable additional debug checks.\n");
	fprintf(stderr, "\t--dump_skiplists\n");
	fprintf(stderr, "\t\tDump skiplists at end of stresstest.\n");
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds, defaults.\n");
	fprintf(stderr, "\t\tto 10.\n");
	fprintf(stderr, "\t--elperupdater\n");
	fprintf(stderr, "\t\tSkiplist elements per updater.  A largish\n");
	fprintf(stderr, "\t\tnumber is required to allow for grace-period\n");
	fprintf(stderr, "\t\tlatency.  Defaults to 2048.\n");
	fprintf(stderr, "\t--no-bal\n");
	fprintf(stderr, "\t\tOmit skiplist balances from stresstest.\n");
	fprintf(stderr, "\t--no-scan\n");
	fprintf(stderr, "\t\tOmit full-skiplist scans from stresstest.\n");
	fprintf(stderr, "\t--nreaders\n");
	fprintf(stderr, "\t\tNumber of reader threads.\n");
	fprintf(stderr, "\t--nupdaters\n");
	fprintf(stderr, "\t\tNumber of updater threads.\n");
	fprintf(stderr, "\t--updatewait\n");
	fprintf(stderr, "\t\tNumber of spin-loop passes per update,\n");
	fprintf(stderr, "\t\tdefaults to -1.  If 0, the updater will not.\n");
	fprintf(stderr, "\t\tdo any updates, except for initialization.\n");
	fprintf(stderr, "\t\tIf negative, the updater waits for the\n");
	fprintf(stderr, "\t\tcorresponding number of milliseconds\n");
	fprintf(stderr, "\t\tbetween updates.\n");
	fprintf(stderr, "\t--valsperupdater\n");
	fprintf(stderr, "\t\tSkiplist key values per updater.  This should\n");
	fprintf(stderr, "\t\tbe about two orders of magnitude less than the\n");
	fprintf(stderr, "\t\tvalue for elsperupdater, defaults to 2048.\n");
	exit(-1);
}

int main(int argc, char *argv[])
{
	int i = 1;
	void (*test_to_do)(void) = NULL;

	smp_init();
	srandom(time(NULL));

	while (i < argc) {
		if (strcmp(argv[i], "--smoketest") == 0) {
			if (i < argc - 1 || i != 1)
				usage(argv[0],
				      "Excess arguments for %s\n", argv[i]);
			smoketest();
			exit(0);

		} else if (strcmp(argv[i], "--stresstest") == 0) {
			abort();
			/* test_to_do = stresstest; */
			if (i != 1)
				usage(argv[0],
				      "Must be first argument: %s\n", argv[i]);
		} else if (strcmp(argv[i], "--cpustride") == 0) {
			cpustride = strtol(argv[++i], NULL, 0);
			if (cpustride <= 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--debug") == 0) {
			debug = 1;
		} else if (strcmp(argv[i], "--dump-skiplists") == 0) {
			dump_skiplists = 1;
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = strtol(argv[++i], NULL, 0);
			if (duration < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--elperupdater") == 0) {
			elperupdater = strtol(argv[++i], NULL, 0);
			if (elperupdater <= 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--no-bal") == 0) {
			no_bal = 1;
		} else if (strcmp(argv[i], "--no-scan") == 0) {
			no_scan = 1;
		} else if (strcmp(argv[i], "--nreaders") == 0) {
			nreaders = strtol(argv[++i], NULL, 0);
			if (nreaders < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nupdaters") == 0) {
			nupdaters = strtol(argv[++i], NULL, 0);
			if (nupdaters < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--updatewait") == 0) {
			updatewait = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--valsperupdater") == 0) {
			valsperupdater = strtol(argv[++i], NULL, 0);
			if (valsperupdater <= 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
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
