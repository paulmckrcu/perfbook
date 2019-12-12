/*
 * hazptrtorture..h: simple user-level performance/stress test of hazard
 *	pointers.
 *
 * Usage:
 * 	./hazptr <nreaders> rperf [ <cpustride> ]
 * 		Run a read-side performance test with the specified
 * 		number of readers spaced by <cpustride>.
 * 		Thus "./hazptr 16 rperf 2" would run 16 readers on
 *		even-numbered CPUs from 0 to 30.
 * 	./hazptr <nupdaters> uperf [ <cpustride> ]
 * 		Run an update-side performance test with the specified
 * 		number of updaters and specified CPU spacing.
 * 	./hazptr <nreaders> perf [ <cpustride> ]
 * 		Run a combined read/update performance test with the specified
 * 		number of readers and one updater and specified CPU spacing.
 * 		The readers run on the low-numbered CPUs and the updater
 * 		of the highest-numbered CPU.
 *
 * The above tests produce output as follows:
 *
 * n_reads: 46008000  n_updates: 146026  nreaders: 2  nupdaters: 1 duration: 1
 * ns/read: 43.4707  ns/update: 6848.1
 *
 * The first line lists the total number of hazard-pointer reads and
 * updates executed during the test, the number of reader threads, the
 * number of updater threads, and the duration of the test in seconds.
 * The second line lists the average duration of each type of operation
 * in nanoseconds, or "nan" if the corresponding type of operation was
 * not performed.
 *
 * 	./hazptr <nreaders> stress
 * 		Run a stress test with the specified number of readers and
 * 		one updater.  None of the threads are affinitied to any
 * 		particular CPU.
 *
 * This test produces output as follows:
 *
 * n_reads: 114633217  n_updates: 3903415  n_mberror: 0
 * hazptr_stress_count: 114618391 14826
 *
 * The first line lists the number of hazard-pointer read and update
 * operations executed, followed by the number of memory-ordering violations
 * (which will be zero in a correct hazard-pointer implementation).
 * The second line lists the number of readers observing progressively
 * more stale data.  A correct hazard-pointer implementation will have
 * only the first two numbers, while a buggy implementation will have
 * additional fields of the form "2:15" where the number before the colon
 * is the pipe stage and the number after the colon is the count.
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
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

/*
 * Test variables.
 */

DEFINE_PER_THREAD(long long, n_reads_pt);
DEFINE_PER_THREAD(long long, n_updates_pt);

long long n_reads = 0LL;
long n_updates = 0L;
atomic_t nthreadsrunning;
char argsbuf[64];

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

#define HAZPTR_READ_RUN 1000

#ifndef NEED_REGISTER_THREAD
#define hazptr_register_thread()		do ; while (0)
#define hazptr_unregister_thread()		do ; while (0)
#endif /* #ifndef NEED_REGISTER_THREAD */

/*
 * Performance test.
 */

void *hazptr_read_perf_test(void *arg)
{
	int i;
	int me = (long)arg;
	int base = me * K;
	long long n_reads_local = 0;
	hazptr_head_t hh;
	hazptr_head_t *hhp = &hh;

	run_on(me);
	hazptr_register_thread();
	atomic_inc(&nthreadsrunning);
	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (goflag == GOFLAG_RUN) {
		for (i = 0; i < HAZPTR_READ_RUN; i++) {
			hp_record((void *)&hhp, &HP[base]);
		}
		n_reads_local += HAZPTR_READ_RUN;
	}
	hp_clear(&HP[base]);
	__get_thread_var(n_reads_pt) += n_reads_local;
	hazptr_thread_exit();
	hazptr_unregister_thread();

	return (NULL);
}

void *hazptr_update_perf_test(void *arg)
{
	long long n_updates_local = 0;

	hazptr_register_thread();
	atomic_inc(&nthreadsrunning);
	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (goflag == GOFLAG_RUN) {
		hazptr_scan();
		n_updates_local++;
	}
	__get_thread_var(n_updates_pt) += n_updates_local;
	hazptr_unregister_thread();
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
	int duration = 1;

	smp_mb();
	while (atomic_read(&nthreadsrunning) < nthreads)
		poll(NULL, 0, 1);
	goflag = GOFLAG_RUN;
	smp_mb();
	sleep(duration);
	smp_mb();
	goflag = GOFLAG_STOP;
	smp_mb();
	wait_all_threads();
	for_each_thread(t) {
		n_reads += per_thread(n_reads_pt, t);
		n_updates += per_thread(n_updates_pt, t);
	}
	printf("n_reads: %lld  n_updates: %ld  nreaders: %d  nupdaters: %d duration: %d\n",
	       n_reads, n_updates, nreaders, nupdaters, duration);
	printf("ns/read: %g  ns/update: %g\n",
	       ((duration * 1000*1000*1000.*(double)nreaders) /
	        (double)n_reads),
	       ((duration * 1000*1000*1000.*(double)nupdaters) /
	        (double)n_updates));
	exit(EXIT_SUCCESS);
}

void perftest(int nreaders, int cpustride)
{
	int i;
	long arg;

	perftestinit();
	for (i = 0; i < nreaders; i++) {
		arg = (long)(i * cpustride);
		create_thread(hazptr_read_perf_test, (void *)arg);
	}
	arg = (long)(i * cpustride);
	create_thread(hazptr_update_perf_test, (void *)arg);
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
		create_thread(hazptr_read_perf_test, (void *)arg);
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
		create_thread(hazptr_update_perf_test, (void *)arg);
	}
	perftestrun(i, 0, nupdaters);
}

/*
 * Stress test.
 */

#define HAZPTR_STRESS_PIPE_LEN (R)

struct hazptr_stress {
	hazptr_head_t hh;
	int inuse;
	int pipe_count;
	int mbtest;
};

struct hazptr_stress hazptr_stress_array[HAZPTR_STRESS_PIPE_LEN];
struct hazptr_stress *hazptr_stress_current;
int hazptr_stress_idx = 0;

int n_mberror = 0;
DEFINE_PER_THREAD(long long [HAZPTR_STRESS_PIPE_LEN + 1], hazptr_stress_count);

void *hazptr_read_stress_test(void *arg)
{
	int me = (int)(long)arg;
	int base = me * K;
	struct hazptr_stress *p;
	int pc;

	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 1);
	hazptr_register_thread();
	while (goflag == GOFLAG_RUN) {
		p = hp_record((void *)&hazptr_stress_current, &HP[base]);
		if (!p)
			continue;
		if (p->mbtest == 0)
			n_mberror++;
		pc = p->pipe_count;
		hp_clear(&HP[base]);
		if ((pc > HAZPTR_STRESS_PIPE_LEN) || (pc < 0))
			pc = HAZPTR_STRESS_PIPE_LEN;
		__get_thread_var(hazptr_stress_count)[pc]++;
		__get_thread_var(n_reads_pt)++;
	}
	hazptr_thread_exit();
	hazptr_unregister_thread();

	return NULL;
}

void hazptr_free(void *ptr)
{
	struct hazptr_stress *p = (struct hazptr_stress *)ptr;

	p->inuse = 0;
}

void *hazptr_update_stress_test(void *arg)
{
	int i;
	struct hazptr_stress *p;
	int sum;

	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 1);
	hazptr_register_thread();
	while (goflag == GOFLAG_RUN) {
		i = hazptr_stress_idx + 1;
		if (i >= HAZPTR_STRESS_PIPE_LEN)
			i = 0;
		p = &hazptr_stress_array[i];
		if (READ_ONCE(p->inuse)) {
			hazptr_stress_idx = i;
			continue;
		}
		p->pipe_count = 0;
		WRITE_ONCE(p->inuse, 1);
		p->mbtest = 0;
		smp_mb();
		p->mbtest = 1;
		smp_mb();
		WRITE_ONCE(hazptr_stress_current, p);
		hazptr_stress_idx = i;
		for (i = 0; i < HAZPTR_STRESS_PIPE_LEN; i++)
			if (!hazptr_stress_array[i].inuse) {
				smp_mb();
				hazptr_stress_array[i].pipe_count++;
			}
		hazptr_free_later(&p->hh);
		p->pipe_count++;
		n_updates++;
	}
	poll(NULL, 0, 100);
	hazptr_scan();
	sum = 0;
	for (i = 0; i < HAZPTR_STRESS_PIPE_LEN; i++)
		if (hazptr_stress_array[i].inuse) {
			sum++;
		}
	if (sum != 0)
		printf("%d of %d hazard pointers in use!\n", sum, HAZPTR_STRESS_PIPE_LEN);
	hazptr_unregister_thread();
	return NULL;
}

void stresstest(int nreaders)
{
	int i;
	int t;
	long long *p;
	long long sum;

	init_per_thread(n_reads_pt, 0LL);
	for_each_thread(t) {
		p = &per_thread(hazptr_stress_count,t)[0];
		for (i = 0; i <= HAZPTR_STRESS_PIPE_LEN; i++)
			p[i] = 0LL;
	}
	hazptr_stress_current = &hazptr_stress_array[0];
	hazptr_stress_current->pipe_count = 0;
	hazptr_stress_current->mbtest = 1;
	for (i = 0; i < nreaders; i++)
		create_thread(hazptr_read_stress_test, NULL);
	create_thread(hazptr_update_stress_test, NULL);
	smp_mb();
	goflag = GOFLAG_RUN;
	smp_mb();
	sleep(10);
	smp_mb();
	goflag = GOFLAG_STOP;
	smp_mb();
	wait_all_threads();
	for_each_thread(t)
		n_reads += per_thread(n_reads_pt, t);
	printf("n_reads: %lld  n_updates: %ld  n_mberror: %d\n",
	       n_reads, n_updates, n_mberror);
	printf("hazptr_stress_count:");
	for (i = 0; i <= HAZPTR_STRESS_PIPE_LEN; i++) {
		sum = 0LL;
		for_each_thread(t) {
			sum += per_thread(hazptr_stress_count, t)[i];
		}
		if (i <= 1)
			printf(" %lld", sum);
		else if (sum != 0)
			printf(" %d:%lld", i, sum);
	}
	printf("\n");
	exit(EXIT_SUCCESS);
}

/*
 * Mainprogram.
 */

void usage(int argc, char *argv[])
{
	fprintf(stderr, "Usage: %s [nreaders [ perf | stress ] ]\n", argv[0]);
	exit(EXIT_FAILURE);
}

int main(int argc, char *argv[])
{
	int nreaders = 1;
	int cpustride = 1;

	smp_init();
	hazptr_init();

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
		else if (strcmp(argv[2], "stress") == 0)
			stresstest(nreaders);
		usage(argc, argv);
	}
	perftest(nreaders, cpustride);
	return 0;
}
