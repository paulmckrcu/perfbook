/*
 * limtorture.h: simple user-level performance/stress test of counters
 *	having upper and lower limits.
 *
 * Usage:
 * 	./countxxx <nreaders> rperf [ <cpustride> ]
 * 		Run a read-side performance test with the specified
 * 		number of counters, running on CPUs spaced by <cpustride>.
 * 		Thus "./count 16 rperf 2" would run 16 readers on even-numbered
 * 		CPUs from 0 to 30.
 * 	./countxxx <nupdaters> uperf [ <cpustride> ]
 * 		Run an update-side performance test with the specified
 * 		number of updaters and specified CPU spacing.
 * 	./countxxx <nreaders> perf [ <cpustride> ]
 * 		Run a combined read/update performance test with the specified
 * 		number of readers and one updater and specified CPU spacing.
 * 		The readers run on the low-numbered CPUs and the updater
 * 		of the highest-numbered CPU.
 * 	./countxxx <nreaders> hog [ <cpustride> ]
 * 		Run a "hog" test in which a "hog" thread holds onto a
 * 		single count in an attempt to prevent other threads from
 * 		getting all count and from returning all count.
 *
 * The above rperf, uperf, and perf tests produce output as follows:
 *
 * n_reads: 824000  n_updates: 75264000  nreaders: 1  nupdaters: 1 duration: 240
 * ns/read: 291.262  ns/update: 3.18878
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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

/*
 * Test variables.
 */

DEFINE_PER_THREAD(long long, n_reads_pt);
DEFINE_PER_THREAD(long long, n_updates_pt);

long long n_reads = 0LL;
long long n_updates = 0LL;
atomic_t nthreadsrunning;
atomic_t n_threads_run_up;
atomic_t n_threads_run_down;
atomic_t n_threads_hog;
int nthreadsexpected;
char argsbuf[64];

#define GOFLAG_INIT	0
#define GOFLAG_HOG	1
#define GOFLAG_RUN_UP	2
#define GOFLAG_RUN_DOWN	3
#define GOFLAG_RUN	4
#define GOFLAG_STOP	5

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

#define COUNT_READ_RUN   1000
#define COUNT_UPDATE_RUN 1000

#ifndef NEED_REGISTER_THREAD
#define count_register_thread()		do ; while (0)
#define count_unregister_thread(n)	do ; while (0)
#endif /* #ifndef NEED_REGISTER_THREAD */

unsigned long garbage = 0; /* disable compiler optimizations. */

/*
 * Up-down limit test.  Count up till failure, wait, then reverse.
 */
void *count_updown_limit(void *arg)
{
	int me = (long)arg;
	long long n_updates_local = 0LL;

	run_on(me);
	count_register_thread();
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) != GOFLAG_RUN_UP)
		poll(NULL, 0, 1);
	while (add_count(1)) {
		n_updates_local++;
	}
	__get_thread_var(n_updates_pt) += n_updates_local;
	smp_mb();
	atomic_inc(&n_threads_run_up);
	while (READ_ONCE(goflag) != GOFLAG_RUN_DOWN)
		poll(NULL, 0, 1);
	n_updates_local = 0LL;
	while (sub_count(1)) {
		n_updates_local--;
	}
	__get_thread_var(n_updates_pt) += n_updates_local;
	smp_mb();
	atomic_inc(&n_threads_run_down);
	while (READ_ONCE(goflag) != GOFLAG_STOP)
		poll(NULL, 0, 1);
	count_unregister_thread(nthreadsexpected);
	return NULL;
}

void *count_updown_hog(void *arg)
{
	int me = (long)arg;
	unsigned long delta;

	run_on(me);
	count_register_thread();
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	delta = num_online_threads() * 20;
	if (!add_count(delta)) {
		fprintf(stderr, "count_updown_hog(): add_count() failed!\n");
		exit(EXIT_FAILURE);
	}
	__get_thread_var(n_updates_pt) += delta;
	smp_mb();
	atomic_inc(&n_threads_hog);
	while (READ_ONCE(goflag) != GOFLAG_STOP)
		poll(NULL, 0, 1);
	count_unregister_thread(nthreadsexpected);
	return NULL;
}

void hogtest(int nreaders, int cpustride)
{
	long arg;
	int i;
	int nthreads = 0;
	int t;

	init_per_thread(n_reads_pt, 0LL);
	init_per_thread(n_updates_pt, 0LL);
	atomic_set(&nthreadsrunning, 0);
	atomic_set(&n_threads_run_up, 0);
	atomic_set(&n_threads_run_down, 0);
	atomic_set(&n_threads_hog, 0);

	for (i = 0; i < nreaders; i++) {
		arg = (long)(i * cpustride);
		create_thread(count_updown_limit, (void *)arg);
		nthreads++;
	}
	arg = (long)(i * cpustride);
	create_thread(count_updown_hog, (void *)arg);
	nthreads++;
	nthreadsexpected = nthreads;
	smp_mb();
	while (atomic_read(&nthreadsrunning) < nthreads)
		poll(NULL, 0, 1);
	goflag = GOFLAG_HOG;
	smp_mb();
	while (atomic_read(&n_threads_hog) < 1)
		poll(NULL, 0, 1);
	smp_mb();
	goflag = GOFLAG_RUN_UP;
	smp_mb();
	while (atomic_read(&n_threads_run_up) < nthreads - 1)
		poll(NULL, 0, 1);
	smp_mb();
	for_each_thread(t)
		n_updates += per_thread(n_updates_pt, t);
	if (n_updates != globalcountmax)
		fprintf(stderr, "FAIL: only reached %lld of %lu\n",
			n_updates, globalcountmax);
	goflag = GOFLAG_RUN_DOWN;
	smp_mb();
	while (atomic_read(&n_threads_run_down) < nthreads - 1)
		poll(NULL, 0, 1);
	smp_mb();
	n_updates = 0LL;
	for_each_thread(t)
		n_updates += per_thread(n_updates_pt, t);
	if (n_updates != 0)
		fprintf(stderr, "FAIL: only reached %lld rather than 0\n",
			n_updates);
	smp_mb();
	goflag = GOFLAG_STOP;
	smp_mb();
	wait_all_threads();
	exit(EXIT_SUCCESS);
}

/*
 * Performance test.
 */

void *count_read_perf_test(void *arg)
{
	int i;
	unsigned long j = 0;
	int me = (long)arg;
	long long n_reads_local = 0LL;

	run_on(me);
	count_register_thread();
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		for (i = COUNT_READ_RUN; i > 0; i--) {
			j += read_count();
			barrier();
		}
		n_reads_local += COUNT_READ_RUN;
	}
	__get_thread_var(n_reads_pt) += n_reads_local;
	count_unregister_thread(nthreadsexpected);
	garbage += j;

	return NULL;
}

void *count_update_perf_test(void *arg)
{
	int i;
	long long n_updates_local = 0LL;

	count_register_thread();
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		for (i = COUNT_UPDATE_RUN; i > 0; i--) {
			add_count(1);
			sub_count(1);
			barrier();
		}
		n_updates_local += COUNT_UPDATE_RUN;
	}
	__get_thread_var(n_updates_pt) += n_updates_local;
	count_unregister_thread(nthreadsexpected);
	return NULL;
}

void perftestinit(int nthreads)
{
	init_per_thread(n_reads_pt, 0LL);
	init_per_thread(n_updates_pt, 0LL);
	atomic_set(&nthreadsrunning, 0);
	nthreadsexpected = nthreads;
}

void perftestrun(int nthreads, int nreaders, int nupdaters)
{
	int exitcode = EXIT_SUCCESS;
	int t;
	int duration = 240;

	smp_mb();
	while (atomic_read(&nthreadsrunning) < nthreads)
		poll(NULL, 0, 1);
	goflag = GOFLAG_RUN;
	smp_mb();
	poll(NULL, 0, duration);
	smp_mb();
	goflag = GOFLAG_STOP;
	smp_mb();
	wait_all_threads();
	for_each_thread(t) {
		n_reads += per_thread(n_reads_pt, t);
		n_updates += per_thread(n_updates_pt, t);
	}
	n_updates *= 2;  /* Each update includes an add and a subtract. */
	if (read_count() != 0) {
		printf("!!! Count mismatch: 0 counted vs. %lu final value\n",
		       read_count());
		exitcode = EXIT_FAILURE;
	}
	printf("n_reads: %lld  n_updates: %lld  nreaders: %d  nupdaters: %d duration: %d\n",
	       n_reads, n_updates, nreaders, nupdaters, duration);
	printf("ns/read: %g  ns/update: %g\n",
	       ((duration * 1000*1000.*(double)nreaders) /
	        (double)n_reads),
	       ((duration * 1000*1000.*(double)nupdaters) /
	        (double)n_updates));
	exit(exitcode);
}

void perftest(int nreaders, int cpustride)
{
	int i;
	long arg;

	perftestinit(nreaders + 1);
	for (i = 0; i < nreaders; i++) {
		arg = (long)(i * cpustride);
		create_thread(count_read_perf_test, (void *)arg);
	}
	arg = (long)(i * cpustride);
	create_thread(count_update_perf_test, (void *)arg);
	perftestrun(i + 1, nreaders, 1);
}

void rperftest(int nreaders, int cpustride)
{
	int i;
	long arg;

	perftestinit(nreaders);
	init_per_thread(n_reads_pt, 0LL);
	for (i = 0; i < nreaders; i++) {
		arg = (long)(i * cpustride);
		create_thread(count_read_perf_test, (void *)arg);
	}
	perftestrun(i, nreaders, 0);
}

void uperftest(int nupdaters, int cpustride)
{
	int i;
	long arg;

	perftestinit(nupdaters);
	init_per_thread(n_reads_pt, 0LL);
	for (i = 0; i < nupdaters; i++) {
		arg = (long)(i * cpustride);
		create_thread(count_update_perf_test, (void *)arg);
	}
	perftestrun(i, 0, nupdaters);
}

/*
 * Mainprogram.
 */

void usage(int argc, char *argv[])
{
	fprintf(stderr,
		"Usage: %s [nreaders [ perf [ cpustride ] ] ]\n", argv[0]);
	fprintf(stderr,
		"Usage: %s [nreaders [ rperf [ cpustride ] ] ]\n", argv[0]);
	fprintf(stderr,
		"Usage: %s [nreaders [ uperf [ cpustride ] ] ]\n", argv[0]);
	fprintf(stderr,
		"Usage: %s [nreaders [ hog [ cpustride ] ] ]\n", argv[0]);
	exit(EXIT_FAILURE);
}

int main(int argc, char *argv[])
{
	int nreaders = 1;
	int cpustride = 1;

	smp_init();
	count_init();

	if (argc > 1) {
		nreaders = strtoul(argv[1], NULL, 0);
		if (argc == 2)
			perftest(nreaders, cpustride);
		if (argc > 3)
			cpustride = strtoul(argv[3], NULL, 0);
		if (strcmp(argv[2], "perf") == 0)
			perftest(nreaders, cpustride);
		else if (strcmp(argv[2], "rperf") == 0)
			rperftest(nreaders, cpustride);
		else if (strcmp(argv[2], "uperf") == 0)
			uperftest(nreaders, cpustride);
		else if (strcmp(argv[2], "hog") == 0)
			hogtest(nreaders, cpustride);
		usage(argc, argv);
	}
	perftest(nreaders, cpustride);
	return 0;
}
