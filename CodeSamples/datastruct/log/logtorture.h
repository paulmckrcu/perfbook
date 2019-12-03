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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
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
int dump_logs = 0;
int nreaders = 0;
int nupdaters = 5;
long valsperupdater = 1024*1024;
int cpustride = 1;
long duration = 10; /* in milliseconds. */
static int debug = 0;

atomic_t nthreads_running;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

struct stresstest_log {
	long index;
	unsigned long val;
};

/* Per-test-thread attribute/statistics structure. */
struct stresstest_attr {
	int myid;
	long long nlookups;
	long long nadds;
	int mycpu;
	long nelements;
	struct stresstest_log *stlp;
	int cat;
};

#define ID_SHIFT (6 * sizeof(long))
#define SEQUENCE_MASK ((1L << ID_SHIFT) - 1)

/* Stress test reader thread. */
void *stresstest_reader(void *arg)
{
	int gf;
	long i;
	long n;
	struct stresstest_attr *pap = arg;
	long long nlookups = 0;
	unsigned long val;

	run_on(pap->mycpu);

	/* Record our presence. */
	atomic_inc(&nthreads_running);

	/* Run the test code. */
	for (;;) {
		gf = ACCESS_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nlookups = 0;
			}
		}
		n = get_log_next_idx(&test_log);
		if (n == 0)
			continue;
		i = random() % n;
		val = get_log_value(&test_log, i);
		if ((val >> ID_SHIFT) >= nupdaters)
			abort();
		if ((val & SEQUENCE_MASK) >= valsperupdater)
			abort();
		nlookups++;
	}
	pap->nlookups = nlookups;
	return NULL;
}

/* Stress test updater thread. */
void *stresstest_updater(void *arg)
{
	long i;
	long idx;
	int gf;
	struct stresstest_attr *pap = arg;
	int myid = pap->myid;
	unsigned long my_shifted_id = ((long)myid) << ID_SHIFT;
	long long nadds = 0;
	unsigned long val;

	run_on(pap->mycpu);

	/* Announce our presence and enter the test loop. */
	atomic_inc(&nthreads_running);
	i = 0;
	while (i < valsperupdater) {
		gf = ACCESS_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing. */
				continue;
			}
		}
		nadds++;
		val = i | my_shifted_id;
		idx = log_append(&test_log, val);
		pap->stlp[i].index = idx;
		pap->stlp[i].val = val;
		i++;
	}

	/* If too much time, complain. */
	if (ACCESS_ONCE(goflag) != GOFLAG_STOP)
		fprintf(stderr,
			"Updater %d completed before test end, %lld adds.\n",
			myid, nadds);

	pap->nelements = i;
	pap->nadds = nadds;

	return NULL;
}

/* Run a performance test. */
void stresstest(void)
{
	struct stresstest_attr *pap;
	int maxcpus = sysconf(_SC_NPROCESSORS_CONF);
	long i;
	long id;
	long long nlookups = 0;
	long long nadds = 0;
	long long starttime;
	long long endtime;
	unsigned long seq;
	unsigned long val;

	BUG_ON(maxcpus <= 0);
	log_init(&test_log, nupdaters * valsperupdater);
	pap = malloc(sizeof(*pap) * (nreaders + nupdaters));
	BUG_ON(pap == NULL);
	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nreaders + nupdaters; i++) {
		pap[i].myid = i < nreaders ? i : i - nreaders;
		pap[i].nlookups = 0;
		pap[i].nadds = 0;
		pap[i].mycpu = (i * cpustride) % maxcpus;
		pap[i].nelements = -1;
		pap[i].stlp = calloc(sizeof(*pap[i].stlp), valsperupdater);
		if (!pap[i].stlp)
			abort();
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
	if (dump_logs) {
		printf("Log dump from parent thread\n:");
		log_dump(&test_log, 0);
		fflush(stdout);
	}

	/* Verify log contents. */
	for (i = 0; i < get_log_next_idx(&test_log); i++) {
		val = get_log_value(&test_log, i);
		id = val >> ID_SHIFT;
		seq = val & SEQUENCE_MASK;
		if (id >= nupdaters)
			abort();
		if (seq >= valsperupdater)
			abort();
		if (pap[id + nreaders].stlp[seq].index != i)
			abort();
		if (pap[id + nreaders].stlp[seq].val != val)
			abort();
	}

	/* Collect stats and output them. */
	for (i = 0; i < nreaders + nupdaters; i++) {
		nlookups += pap[i].nlookups;
		nadds += pap[i].nadds;
	}
	printf("nlookups: %lld  nadds: %lld  duration: %g\n",
	       nlookups, nadds, starttime / 1000.);
	printf("ns/read+scan: %g  ns/update: %g\n",
	       (starttime * 1000. * (double)nreaders) / (double)nlookups,
	       ((starttime * 1000. * (double)nupdaters) / (double)nadds));

	free(pap);
}

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
	fprintf(stderr, "\t--dump-logs\n");
	fprintf(stderr, "\t\tDump skiplists at end of stresstest.\n");
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds, defaults.\n");
	fprintf(stderr, "\t\tto 10.\n");
	fprintf(stderr, "\t--no-bal\n");
	fprintf(stderr, "\t\tOmit skiplist balances from stresstest.\n");
	fprintf(stderr, "\t--nreaders\n");
	fprintf(stderr, "\t\tNumber of reader threads.\n");
	fprintf(stderr, "\t--nupdaters\n");
	fprintf(stderr, "\t\tNumber of updater threads.\n");
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
			test_to_do = stresstest;
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
		} else if (strcmp(argv[i], "--dump-log") == 0) {
			dump_logs = 1;
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = strtol(argv[++i], NULL, 0);
			if (duration < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
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
