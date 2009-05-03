/*
 * counttorture.h: simple user-level performance/stress test of counters.
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
 *
 * The above tests produce output as follows @@@:
 *
 * n_reads: 46008000  n_updates: 146026  nreaders: 2  nupdaters: 1 duration: 1
 * ns/read: 43.4707  ns/update: 6848.1
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

/*
 * Test variables.
 */

DEFINE_PER_THREAD(long long, n_reads_pt);
DEFINE_PER_THREAD(long long, n_updates_pt);

long long n_reads = 0LL;
long long n_updates = 0LL;
atomic_t nthreadsrunning;
char argsbuf[64];

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

#define COUNT_READ_RUN   1000
#define COUNT_UPDATE_RUN 1000

#ifndef NEED_REGISTER_THREAD
#define count_register_thread()		do ; while (0)
#define count_unregister_thread()	do ; while (0)
#endif /* #ifndef NEED_REGISTER_THREAD */

/*
 * Performance test.
 */

void *count_read_perf_test(void *arg)
{
	int i;
	long j;
	int me = (long)arg;
	long long n_reads_local = 0LL;

	run_on(me);
	count_register_thread();
	atomic_inc(&nthreadsrunning);
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		for (i = COUNT_READ_RUN; i > 0; i--) {
			j += read_count();
		}
		n_reads_local += COUNT_READ_RUN;
	}
	__get_thread_var(n_reads_pt) += n_reads_local;
	count_unregister_thread();

	return (NULL);
}

void *count_update_perf_test(void *arg)
{
	int i;
	long long n_updates_local = 0LL;

	count_register_thread();
	atomic_inc(&nthreadsrunning);
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		for (i = COUNT_UPDATE_RUN; i > 0; i--) {
			inc_count();
		}
		n_updates_local += COUNT_UPDATE_RUN;
	}
	__get_thread_var(n_updates_pt) += n_updates_local;
	count_unregister_thread();
	return NULL;
}

void perftestinit(void)
{
	init_per_thread(n_reads_pt, 0LL);
	init_per_thread(n_updates_pt, 0LL);
	atomic_set(&nthreadsrunning, 0);
}

void perftestrun(int nthreads, int nreaders, int nupdaters)
{
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
	if (n_updates != read_count())
		printf("!!! Count mismatch: %lld counted vs. %ld final value\n",
		       n_updates, read_count());
	printf("n_reads: %lld  n_updates: %lld  nreaders: %d  nupdaters: %d duration: %d\n",
	       n_reads, n_updates, nreaders, nupdaters, duration);
	printf("ns/read: %g  ns/update: %g\n",
	       ((duration * 1000*1000.*(double)nreaders) /
	        (double)n_reads),
	       ((duration * 1000*1000.*(double)nupdaters) /
	        (double)n_updates));
	exit(0);
}

void perftest(int nreaders, int cpustride)
{
	int i;
	long arg;

	perftestinit();
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

	perftestinit();
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

	perftestinit();
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
	exit(-1);
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
		usage(argc, argv);
	}
	perftest(nreaders, cpustride);
}
