/*
 * cachetorture.c: Simple rough-and-ready measurement of cache latencies
 *
 * This test produces output as follows:
 *
 * ./cachetorture checkcmpxchg CPUs 0 1 duration: 240255 ops/us: 8.71474
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

static atomic_t cachectr __attribute__((__aligned__(CACHE_LINE_SIZE)));
DEFINE_SPINLOCK(my_lock);

static void cachetestinit(void *mycpu_in)
{
	run_on((intptr_t)mycpu_in);
	BUG_ON(atomic_xchg(&cachectr, 0) != 0);  // Pull to cache.
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		xchg(&garbage, READ_ONCE(garbage) + 1);
}

static void *atomicinc0(void *mycpu_in)
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

static void *atomicinc1(void *mycpu_in)
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

static void *blindcmpxchg0(void *mycpu_in)
{
	unsigned long snap = 0;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		while (atomic_cmpxchg(&cachectr, snap, snap + 1) != snap)
			if (READ_ONCE(goflag) != GOFLAG_RUN)
				break;
		snap += 2;
	}
	return NULL;
}

static void *blindcmpxchg1(void *mycpu_in)
{
	unsigned long snap = 1;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		while (atomic_cmpxchg(&cachectr, snap, snap + 1) != snap)
			if (READ_ONCE(goflag) != GOFLAG_RUN)
				break;
		snap += 2;
	}
	return NULL;
}

static void *cmpxchg0(void *mycpu_in)
{
	unsigned long snap;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		snap = atomic_read(&cachectr);
		if (!(snap & 0x1))
			continue;
		while (atomic_cmpxchg(&cachectr, snap, snap + 1) != snap)
			if (READ_ONCE(goflag) != GOFLAG_RUN)
				break;
	}
	return NULL;
}

static void *cmpxchg1(void *mycpu_in)
{
	unsigned long snap;

	cachetestinit(mycpu_in);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		snap = atomic_read(&cachectr);
		if (snap & 0x1)
			continue;
		while (atomic_cmpxchg(&cachectr, snap, snap + 1) != snap)
			if (READ_ONCE(goflag) != GOFLAG_RUN)
				break;
	}
	return NULL;
}

static void *write0(void *mycpu_in)
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

static void *write1(void *mycpu_in)
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

static void localcmpxchg(int cpu)
{
	int i;
	int snap = 0;

	run_on(cpu);
	BUG_ON(atomic_xchg(&cachectr, 0) != 0);  // Pull to cache.
	start = (double)get_microseconds();
	for (i = 0; i < 10 * 1000 * 1000; i++) {
		BUG_ON(atomic_cmpxchg(&cachectr, snap, snap + 1) != snap);
		snap++;
	}
	stop = (double)get_microseconds();
}

static void locallock(int cpu)
{
	int i;

	run_on(cpu);
	BUG_ON(atomic_xchg(&cachectr, 0) != 0);  // Pull to cache.
	start = (double)get_microseconds();
	for (i = 0; i < 10 * 1000 * 1000; i++) {
		spin_lock(&my_lock);
		atomic_set(&cachectr, atomic_read(&cachectr) + 1);
		spin_unlock(&my_lock);
	}
	stop = (double)get_microseconds();
}

/*
 * Mainprogram.
 */

void usage(int argc, char *argv[])
{
	fprintf(stderr,
		"Usage:\t%s atomicinc [ <CPU> [ <CPU> ] ]\n", argv[0]);
	fprintf(stderr,
		"\t%s blindcmpxchg [ <CPU> [ <CPU> ] ]\n", argv[0]);
	fprintf(stderr,
		"\t%s cmpxchg [ <CPU> [ <CPU> ] ]\n", argv[0]);
	fprintf(stderr,
		"\t%s localcmpxchg [ <CPU> [ <CPU> ] ]\n", argv[0]);
	fprintf(stderr,
		"\t%s locallock [ <CPU> [ <CPU> ] ]\n", argv[0]);
	fprintf(stderr,
		"\t%s write [ <CPU> [ <CPU> ] ]\n", argv[0]);
	fprintf(stderr, "localcmpxchg and locallock ignore second CPU.\n");
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
	if (strcmp(argv[1], "atomicinc") == 0)
		cachetest(atomicinc0, atomicinc1, cpu0, cpu1);
	else if (strcmp(argv[1], "blindcmpxchg") == 0)
		cachetest(blindcmpxchg0, blindcmpxchg1, cpu0, cpu1);
	else if (strcmp(argv[1], "cmpxchg") == 0)
		cachetest(cmpxchg0, cmpxchg1, cpu0, cpu1);
	else if (strcmp(argv[1], "write") == 0)
		cachetest(write0, write1, cpu0, cpu1);
	else if (strcmp(argv[1], "locallock") == 0)
		locallock(cpu0);
	else if (strcmp(argv[1], "localcmpxchg") == 0)
		localcmpxchg(cpu0);
	else
		usage(argc, argv);
	printf("%s %s CPUs %d %d duration: %g ns/op: %g\n",
	       argv[0], argv[1], cpu0, cpu1, stop - start,
	       1000. * (stop - start) / (double)atomic_read(&cachectr));
	return 0;
}
