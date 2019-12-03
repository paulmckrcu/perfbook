/*
 * seqlocktorture.c: simple user-level performance/stress test of sequence lock.
 *
 * Usage:
 *	./seqlocktorture nreaders [ nwriters [ nelems [ cpustride ] ] ]
 *		Run a performance test with the specified
 * 		number of readers and writers, running on CPUs spaced
 *		by <cpustride>.  Thus "./seqlocktorture 8 8 2" would
 *		run 8 readers and 8 writers on even-numbered CPUs from
 *		0 to 30.
 *
 * The above tests produce output as follows:
 *
 * n_reads: 824000  n_writes: 75264000  nreaders: 1  nwriters: 1 duration: 240
 * ns/read: 291.262  ns/write: 3.18878
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
 * Copyright (c) 2011-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include "seqlock.h"

/*
 * Test variables.
 */

DEFINE_PER_THREAD(long long, n_reads_pt);
DEFINE_PER_THREAD(long long, n_read_retries_pt);
DEFINE_PER_THREAD(long long, n_read_errs_pt);
DEFINE_PER_THREAD(long long, n_writes_pt);

atomic_t nthreadsrunning;
int nthreadsexpected;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

#define COUNT_READ_RUN   1000
#define COUNT_UPDATE_RUN 1000

#define TESTARRAY_SIZE (1024*1024)
unsigned long testarray[TESTARRAY_SIZE];
seqlock_t test_seqlock;
int n_elems = TESTARRAY_SIZE;

/*
 * Performance/stress test.
 */

void *seqlock_read_test(void *arg)
{
	int i;
	int j;
	int me = (long)arg;
	long long n_errs_local = 0LL;
	long long n_reads_local = 0LL;
	long long n_retries_local = 0LL;
	long long n_retries_local_cur = 0LL;
	unsigned long old;
	unsigned long seq;

	run_on(me);
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		for (i = COUNT_READ_RUN; i > 0; i--) {
			n_retries_local_cur = -1;
			do {
				seq = read_seqbegin(&test_seqlock);
				old = testarray[0];
				n_errs_local = 0;
				n_retries_local_cur++;
				for (j = 1; j < n_elems; j++) {
					if (old + 1 != testarray[j])
						n_errs_local++;
					old = testarray[j];
				}
			} while (read_seqretry(&test_seqlock, seq));
			n_retries_local += n_retries_local_cur;
			barrier();
		}
		n_reads_local += COUNT_READ_RUN;
	}
	__get_thread_var(n_reads_pt) += n_reads_local;
	__get_thread_var(n_read_retries_pt) += n_retries_local;
	__get_thread_var(n_read_errs_pt) += n_errs_local;

	return (NULL);
}

void *seqlock_write_test(void *arg)
{
	int i;
	int j;
	int me = (long)arg;
	long long n_writes_local = 0LL;

	run_on(me);
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		for (i = COUNT_UPDATE_RUN; i > 0; i--) {
			write_seqlock(&test_seqlock);
			for (j = 0; j < n_elems; j++)
				testarray[j]++;
			write_sequnlock(&test_seqlock);
			barrier();
		}
		n_writes_local += COUNT_UPDATE_RUN;
	}
	__get_thread_var(n_writes_pt) += n_writes_local;
	return NULL;
}

void perftestinit(int nthreads)
{
	int i;

	init_per_thread(n_reads_pt, 0LL);
	init_per_thread(n_read_retries_pt, 0LL);
	init_per_thread(n_read_errs_pt, 0LL);
	init_per_thread(n_writes_pt, 0LL);
	atomic_set(&nthreadsrunning, 0);
	nthreadsexpected = nthreads;
	seqlock_init(&test_seqlock);
	for (i = 0; i < TESTARRAY_SIZE; i++)
		testarray[i] = i;
}

void perftestrun(int nthreads, int nreaders, int nwriters)
{
	int t;
	int duration = 240;
	long long n_reads = 0LL;
	long long n_read_retries = 0LL;
	long long n_read_errs = 0LL;
	long long n_writes = 0LL;

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
		n_read_retries += per_thread(n_read_retries_pt, t);
		n_read_errs += per_thread(n_read_errs_pt, t);
		n_writes += per_thread(n_writes_pt, t);
	}
	if (n_read_errs != 0)
		printf("!!! read-side errors detected: %lld\n", n_read_errs);
	printf("n_reads: %lld n_read_retries: %lld n_writes: %lld nreaders: %d  nwriters: %d n_elems: %d duration: %d\n",
	       n_reads, n_read_retries, n_writes, nreaders, nwriters, n_elems, duration);
	printf("ns/read: %g  ns/write: %g\n",
	       ((duration * 1000*1000.*(double)nreaders) /
	        (double)n_reads),
	       ((duration * 1000*1000.*(double)nwriters) /
	        (double)n_writes));
	exit(EXIT_SUCCESS);
}

void perftest(int nreaders, int nwriters, int cpustride)
{
	int i;
	long arg;

	perftestinit(nreaders + nwriters + 1);
	for (i = 0; i < nreaders; i++) {
		arg = (long)(i * cpustride);
		create_thread(seqlock_read_test, (void *)arg);
	}
	for (; i < nreaders + nwriters; i++) {
		arg = (long)(i * cpustride);
		create_thread(seqlock_write_test, (void *)arg);
	}
	perftestrun(i, nreaders, nwriters);
}

/*
 * Mainprogram.
 */

void usage(int argc, char *argv[])
{
	fprintf(stderr,
		"Usage: %s [nreaders [ nwriters [ nelems [ cpustride ] ] ] ]\n",
		argv[0]);
	exit(EXIT_FAILURE);
}

int main(int argc, char *argv[])
{
	int nreaders = 1;
	int nwriters = 0;
	int cpustride = 1;
	int nelems_in;

	smp_init();

	if (argc > 1)
		nreaders = strtoul(argv[1], NULL, 0);
	if (argc > 2)
		nwriters = strtoul(argv[2], NULL, 0);
	if (argc > 3) {
		nelems_in = strtol(argv[3], NULL, 0);
		if (nelems_in > 0 && nelems_in <= TESTARRAY_SIZE)
			n_elems = nelems_in;
	}
	if (argc > 4)
		cpustride = strtoul(argv[4], NULL, 0);
	if (argc <= 5)
		perftest(nreaders, nwriters, cpustride);
	else
		usage(argc, argv);
	return 0;
}
