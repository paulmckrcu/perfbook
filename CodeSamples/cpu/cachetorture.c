/*
 * cachetorture.c: Simple rough-and-ready measurement of cache latencies
 *
 * Usage:
 * 	./countxxx checkwrite [ <CPU> [ <CPU> ] ]
 * 		Run a read-side performance test with the specified
 * 		number of counters, running on CPUs spaced by <cpustride>.
 * 		Thus "./count 16 rperf 2" would run 16 readers on even-numbered
 * 		CPUs from 0 to 30.
 * 	./countxxx <nupdaters> uperf [ <cpustride> ]
 * 		Run an update-side performance test with the specified
 * 		number of updaters and specified CPU spacing.
 * 	./countxxx <nupdaters> perf [ <cpustride> ]
 * 		Run a combined read/update performance test with the specified
 * 		number of readers and one updater and specified CPU spacing.
 * 		The readers run on the low-numbered CPUs and the updater
 * 		of the highest-numbered CPU.
 *
 * The above tests produce output as follows:
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

#include "../api.h"

/*
 * Test variables.
 */

atomic_t nthreadsrunning;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

#define COUNT_READ_RUN   1000
#define COUNT_UPDATE_RUN 1000

unsigned long garbage = 0; /* disable compiler optimizations. */

static int duration = 240;
static double start;
static double stop;

static atomic_t cachectr;

static void cachetestinit(void *mycpu_in)
{
	run_on((intptr_t)mycpu_in);
	BUG_ON(atomic_xchg(&cachectr, 0) != 0);  // Pull to cache.
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		xchg(&garbage, READ_ONCE(garbage) + 1);
}

static void *checkatomicinc0(void *mycpu_in)
{
	unsigned long snap;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		snap = atomic_read(&cachectr);
		if (!(snap & 0x1))
			continue;
		atomic_inc(&cachectr);
	}
	return NULL;
}

static void *checkatomicinc1(void *mycpu_in)
{
	unsigned long snap;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		snap = atomic_read(&cachectr);
		if (snap & 0x1)
			continue;
		atomic_inc(&cachectr);
	}
	return NULL;
}

static void *checkbcmpxchg0(void *mycpu_in)
{
	unsigned long snap = 0;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		while (atomic_cmpxchg(&cachectr, snap, snap + 1) != snap)
			continue;
		snap += 2;
	}
	return NULL;
}

static void *checkbcmpxchg1(void *mycpu_in)
{
	unsigned long snap = 1;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		while (atomic_cmpxchg(&cachectr, snap, snap + 1) != snap)
			continue;
		snap += 2;
	}
	return NULL;
}

static void *checkcmpxchg0(void *mycpu_in)
{
	unsigned long snap;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		snap = atomic_read(&cachectr);
		if (!(snap & 0x1))
			continue;
		while (atomic_cmpxchg(&cachectr, snap, snap + 1) != snap)
			continue;
	}
	return NULL;
}

static void *checkcmpxchg1(void *mycpu_in)
{
	unsigned long snap;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		snap = atomic_read(&cachectr);
		if (snap & 0x1)
			continue;
		while (atomic_cmpxchg(&cachectr, snap, snap + 1) != snap)
			continue;
	}
	return NULL;
}

static void *checkwrite0(void *mycpu_in)
{
	unsigned long snap;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		snap = atomic_read(&cachectr);
		if (snap & 0x1)
			atomic_set(&cachectr, snap + 1);
	}
	return NULL;
}

static void *checkwrite1(void *mycpu_in)
{
	unsigned long snap;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		snap = atomic_read(&cachectr);
		if (!(snap & 0x1))
			atomic_set(&cachectr, snap + 1);
	}
	return NULL;
}

static void cachetest(void *(*checkwrite0)(void *),
		      void *(*checkwrite1)(void *),
		      uintptr_t cpu0, uintptr_t cpu1)
{
	create_thread(checkwrite0, (void *)cpu0);
	create_thread(checkwrite1, (void *)cpu1);
	while (atomic_read(&nthreadsrunning) < 2)
		poll(NULL, 0, 1);
	start = (double)get_microseconds();
	goflag = GOFLAG_RUN;
	smp_mb();
	poll(NULL, 0, duration);
	smp_mb();
	goflag = GOFLAG_STOP;
	stop = (double)get_microseconds();
	smp_mb();
	wait_all_threads();
}

/*
 * Mainprogram.
 */

void usage(int argc, char *argv[])
{
	fprintf(stderr,
		"Usage: %s checkwrite [ <CPU> [ <CPU> ] ]\n", argv[0]);
	fprintf(stderr,
		"Usage: %s checkbcmpxchg [ <CPU> [ <CPU> ] ]\n", argv[0]);
	fprintf(stderr,
		"Usage: %s checkatomicinc [ <CPU> [ <CPU> ] ]\n", argv[0]);
	exit(EXIT_FAILURE);
}

int main(int argc, char *argv[])
{
	int cpu0 = 0;
	int cpu1 = 1;

	smp_init();

	if (argc <= 1)
		usage(argc, argv);
	if (argc > 2) {
		cpu0 = strtoul(argv[2], NULL, 0);
		if (argc == 3)
			cpu1 = cpu0 + 1;
		else if (argc == 4)
			cpu1 = strtoul(argv[3], NULL, 0);
		else
			usage(argc, argv);
	}
	if (strcmp(argv[1], "checkwrite") == 0)
		cachetest(checkwrite0, checkwrite1, cpu0, cpu1);
	else if (strcmp(argv[1], "checkbcmpxchg") == 0)
		cachetest(checkbcmpxchg0, checkbcmpxchg1, cpu0, cpu1);
	else if (strcmp(argv[1], "checkcmpxchg") == 0)
		cachetest(checkcmpxchg0, checkcmpxchg1, cpu0, cpu1);
	else if (strcmp(argv[1], "checkatomicinc") == 0)
		cachetest(checkatomicinc0, checkatomicinc1, cpu0, cpu1);
	else
		usage(argc, argv);
	printf("%s %s CPUs %d %d duration: %g ops/us: %g\n",
	       argv[0], argv[1], cpu0, cpu1, stop - start,
	       ((double)atomic_read(&cachectr)) / ((2. * (stop - start))));
	return 0;
}
