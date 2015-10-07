/*
 * Program to test sequences of loads and stores with and without the
 * benefit of memory barriers.  This header file provides definitions
 * and control flow.  It is to be included from a file providing the
 * actual tests.
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
 * Copyright (C) IBM Corporation, 2006
 *
 * Authors: Paul E. McKenney <paulmck@us.ibm.com>
 * 	    Raúl E. Silvera<rauls@ca.ibm.com>
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#define __USE_GNU
#include <sched.h>
#include <pthread.h>
#include <ucontext.h>
#include <sys/types.h>
#include <sys/mman.h>

/*
 * Variables controlled (or to be controlled) by command-line arguments.
 */

long cpuoffset = 0;
long jitter = 0;
long ncycles = 64;
long noise_size = 8;
long test_cycle_tb_mask	= 0xff;		/* These TB bits 0: start rep */

/*
 * Architectural constants.
 */

#define CACHE_LINE_SIZE		128
#define NOISE_SIZE_MAX		32
#define MAX_CPUS		32

/*
 * Dump the configuration, abort if ill-formed.
 * Though if ill-formed, probably couldn't compile anyway...
 */
void dump_config(char *prog)
{
	int error = 0;

	printf("%s configuration:\n", prog);
	printf("CPU offset: %d\n", cpuoffset);
	printf("Number of test cycles: %d\n", ncycles);
	printf("Timing jitter mask: %#x TB ticks\n", jitter);
	printf("Cache-line size: %d bytes\n", CACHE_LINE_SIZE);
	printf("Store-buffer max data size: %d cache lines\n", NOISE_SIZE_MAX);
	printf("Maximum number of CPUs: %d\n", MAX_CPUS);
	printf("Store-buffer data size: %d cache lines\n", noise_size);
	printf("Start each rep when these bits of TB are zero: %x\n",
	       test_cycle_tb_mask);
	if ((test_cycle_tb_mask & (test_cycle_tb_mask + 1)) != 0) {
		printf("test_cycle_tb_mask must be consecutive low-order bits"
		       " (e.g., 0xff)\n");
		error = 1;
	}
	fflush(stdout);
	if (error != 0)
		exit(-1);
}

#include "arch.h"

/*
 * Get a timestamp far enough ahead in time to allow people to get lined up.
 */
static long next_test_cycle_start(void)
{
	return (gettb() + 16 * test_cycle_tb_mask + 1) & ~test_cycle_tb_mask;
}

/*
 * Spin until the time-base register reaches the specified value.
 */
static void spin_tb(long targettb)
{
	while (gettb() - targettb < 0)
		barrier();
}

/*
 * Data for memory ordering tests.
 */

struct cacheline {
	long value;
	char vfill[CACHE_LINE_SIZE - sizeof(long)];
};

struct ctxt_state {
	double	aalign;
	long	n;
	long	n1;
	long	n2;
	char	nfill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	a;
	long	a1;	/* Interfere with a, if desired. */
	long	a2;
	char	afill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	b;
	long	b1;
	long	b2;
	char	bfill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	c;
	long	c1;
	long	c2;
	char	cfill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	d;
	long	d1;
	long	d2;
	char	dfill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	e;
	long	e1;
	long	e2;
	char	efill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	v;
	long	v1;
	long	v2;
	char	vfill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	x;
	long	x1;
	long	x2;
	char	xfill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	y;
	long	y1;
	long	y2;
	char	yfill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	z;
	long	z1;
	long	z2;
	char	zfill[CACHE_LINE_SIZE - 3 * sizeof(long)];
	long	starttime;
	long	s;
	long	f;
	long	oldn;
	long	anomalies;
	long	badcount;
	long	oldbadcount;
	char	miscfill[CACHE_LINE_SIZE - 7 * sizeof(long)];
	struct cacheline fillstorebuffer[NOISE_SIZE_MAX];
} state = { 0 };

/* Ensure that the two arguments are in the same cache line. */

#define assert_same_cache_line(a, b) \
do { \
	if ((((long)&(a)) ^ ((long)&(b))) & ~(CACHE_LINE_SIZE - 1)) { \
		fprintf(stderr, \
			"" #a "=%lx, " #b "=%lx not in same cache line!!!\n", \
			(long)&(a), (long)&(b)); \
		exit(-1); \
	} \
} while (0)

/* Ensure that the two arguments are in different cache lines. */

#define assert_different_cache_line(a, b) \
do { \
	if (((((long)&(a)) ^ ((long)&(b))) & ~(CACHE_LINE_SIZE - 1)) == 0) { \
		fprintf(stderr, \
			"" #a "=%lx, " #b "=%lx false sharing!!!\n", \
			(long)&(a), (long)&(b)); \
		exit(-1); \
	} \
} while (0)

/*
 * Make sure that our data structure landed in memory as desired.
 */
void validate_cache_layout(void)
{
	assert_same_cache_line(state.n, state.n1);
	assert_different_cache_line(state.n, state.a);
	assert_same_cache_line(state.a, state.a1);
	assert_different_cache_line(state.a, state.b);
	assert_same_cache_line(state.b, state.b1);
	assert_different_cache_line(state.b, state.c);
	assert_same_cache_line(state.c, state.c1);
	assert_different_cache_line(state.c, state.d);
	assert_same_cache_line(state.d, state.d1);
	assert_different_cache_line(state.d, state.x);
	assert_same_cache_line(state.x, state.x1);
	assert_different_cache_line(state.x, state.y);
	assert_same_cache_line(state.y, state.y1);
	assert_different_cache_line(state.y, state.z);
	assert_same_cache_line(state.z, state.z1);
	assert_different_cache_line(state.z, state.starttime);
	assert_different_cache_line(state.z, state.oldn);
	assert_different_cache_line(state.z, state.s);
	assert_different_cache_line(state.z, state.x);
	assert_different_cache_line(state.z, state.anomalies);
	assert_different_cache_line(state.z, state.badcount);
}

/*
 * Thread-control variables and functions.
 */

int all_threads_created = 0;
int num_threads_created = 0;
int num_threads_ready = 0;
typedef pthread_mutex_t spinlock_t;
spinlock_t threadlock = PTHREAD_MUTEX_INITIALIZER;

void spin_lock(pthread_mutex_t *lp)
{
	if (pthread_mutex_lock(lp) != 0) {
		perror("pthread_mutex_lock");
		exit(-1);
	}
}

void spin_unlock(pthread_mutex_t *lp)
{
	if (pthread_mutex_unlock(lp) != 0) {
		perror("pthread_mutex_unlock");
		exit(-1);
	}
}

pthread_t create_thread(void *(*func)(void *), void *arg)
{
	pthread_t id;

	if (pthread_create(&id, NULL, func, arg) != 0) {
		perror("pthread_create");
		exit(-1);
	}
	return id;
}

void *wait_thread(pthread_t id)
{
	void *retval;

	if (pthread_join(id, &retval) != 0) {
		perror("pthread_join");
		exit(-1);
	}
	return (retval);
}

/*
 * Make the current thread run on the specified CPU, courtesy Paul Mackerras.
 */
void runon(int cpu)
{
	cpu_set_t cset;

	CPU_ZERO(&cset);
	CPU_SET(cpu, &cset);
	if (sched_setaffinity(0, sizeof(cpu_set_t), &cset) < 0) {
		perror("setaffinity");
		exit(1);
	}
}

/*
 * Wait until all threads are spawned, put each on the proper CPU, and go.
 */
void startyourengines(int mycpu)
{
	runon(mycpu);
	while (!all_threads_created)
		barrier();
	poll(NULL, 0, 1);	/* Let parent get out of the way. */
	spin_lock(&threadlock);
	num_threads_ready++;
	spin_unlock(&threadlock);
	while (num_threads_ready < num_threads_created)
		barrier();
}

struct cache_preload {
	int thread;
	long *var;
};

struct cache_preload cache_preload[];

void preload(int mythread)
{
	int i;

	i = 0;
	while (cache_preload[i].var != NULL) {
		if (cache_preload[i].thread == mythread)
			*cache_preload[i].var = 0;
		i++;
	}
}

void printfullstate(void)
{
	long t = gettb();
	time_t tt;

	tt = time(NULL);
	printf("A = %ld %ld %ld\n", state.a, state.a1, state.a2);
	printf("B = %ld %ld %ld\n", state.b, state.b1, state.b2);
	printf("C = %ld %ld %ld\n", state.c, state.c1, state.c2);
	printf("D = %ld %ld %ld\n", state.d, state.d1, state.d2);
	printf("E = %ld %ld %ld\n", state.e, state.e1, state.e2);
	printf("V = %ld %ld %ld\n", state.v, state.v1, state.v2);
	printf("X = %ld %ld %ld\n", state.x, state.x1, state.x2);
	printf("Y = %ld %ld %ld\n", state.y, state.y1, state.y2);
	printf("Z = %ld %ld %ld\n", state.z, state.z1, state.z2);
}

struct thread_assignment {
	int cpu;
	void *(*thread)(void *);
	pthread_t id;
};

struct thread_assignment thread_assignment[];

/*
 */

void *thread_0(void *me_in)
{
	struct cacheline fillstorebuffer[NOISE_SIZE_MAX];
	int i;
	int mycpu = (int)me_in;

	startyourengines(mycpu);
	while (state.n < ncycles) {
		state.oldbadcount = state.badcount;
		state.oldn = state.n; /* set up for upcoming cycle. */
		state.a = state.b = state.c = state.d = state.x =
			state.y = state.z = 0;
		state.a1 = state.b1 = state.c1 = state.d1 = 0;
		state.f = num_threads_created - 1;
		state.s = num_threads_created - 1;
#ifdef INIT_VARS_EACH_CYCLE
		INIT_VARS_EACH_CYCLE;
#endif
		preload(0);
		hwsync();
		state.starttime = next_test_cycle_start();
		hwsync();
		while (state.s)
			barrier();
		hwsync();
		state.n++;
		spin_tb(state.starttime + (state.n & jitter));
		for (i = 0; i < noise_size; i++)
			fillstorebuffer[i].value++;
		lwsync();
		THREAD_0;
		lwsync();
		while (state.f)
			barrier();  /* should spin in cache. */
		hwsync();
		if (state.oldbadcount == 0 && state.badcount != 0) {
			printfullstate();
		}
	}
	return NULL;
}

/*
 */

void *thread_1(void *me_in)
{
	struct cacheline fillstorebuffer[NOISE_SIZE_MAX];
	int i;
	int mycpu = (int)me_in;
	long oldtb;
	int sum = 0;

	oldtb = state.starttime;
	hwsync();
	startyourengines(mycpu);
	while (state.n < ncycles) {
		while (oldtb == state.starttime) {
			if (state.n >= ncycles)
				return NULL;
			barrier();
		}
		oldtb = state.starttime;
		preload(1);
		hwsync();
		atomic_dec(&state.s);
		hwsync();
		spin_tb(state.starttime + (state.n & jitter));
		hwsync();
		for (i = 0; i < noise_size; i++)
			fillstorebuffer[i].value++;
		THREAD_1;
		lwsync();
		atomic_dec(&state.f);
		hwsync();
	}
	return NULL;
}

/*
 */
#ifdef THREAD_2

void *thread_2(void *me_in)
{
	struct cacheline fillstorebuffer[NOISE_SIZE_MAX];
	int i;
	int mycpu = (int)me_in;
	long oldtb;
	int sum = 0;

	oldtb = state.starttime;
	hwsync();
	startyourengines(mycpu);
	while (state.n < ncycles) {
		while (oldtb == state.starttime) {
			if (state.n >= ncycles)
				return NULL;
			barrier();
		}
		oldtb = state.starttime;
		preload(2);
		hwsync();
		atomic_dec(&state.s);
		hwsync();
		spin_tb(state.starttime + (state.n & jitter));
		hwsync();
		for (i = 0; i < noise_size; i++)
			fillstorebuffer[i].value++;
		THREAD_2;
		lwsync();
		atomic_dec(&state.f);
		hwsync();
	}
	return NULL;
}

#endif /* #ifdef THREAD_2 */

/*
 */
#ifdef THREAD_3

void *thread_3(void *me_in)
{
	struct cacheline fillstorebuffer[NOISE_SIZE_MAX];
	int i;
	int mycpu = (int)me_in;
	long oldtb;
	int sum = 0;

	oldtb = state.starttime;
	hwsync();
	startyourengines(mycpu);
	while (state.n < ncycles) {
		while (oldtb == state.starttime) {
			if (state.n >= ncycles)
				return NULL;
			barrier();
		}
		oldtb = state.starttime;
		preload(3);
		hwsync();
		atomic_dec(&state.s);
		hwsync();
		spin_tb(state.starttime + (state.n & jitter));
		hwsync();
		for (i = 0; i < noise_size; i++)
			fillstorebuffer[i].value++;
		THREAD_3;
		lwsync();
		atomic_dec(&state.f);
		hwsync();
	}
	return NULL;
}

#endif /* #ifdef THREAD_3 */

/*
 */
#ifdef THREAD_4

void *thread_4(void *me_in)
{
	struct cacheline fillstorebuffer[NOISE_SIZE_MAX];
	int i;
	int mycpu = (int)me_in;
	long oldtb;
	int sum = 0;

	oldtb = state.starttime;
	hwsync();
	startyourengines(mycpu);
	while (state.n < ncycles) {
		while (oldtb == state.starttime) {
			if (state.n >= ncycles)
				return NULL;
			barrier();
		}
		oldtb = state.starttime;
		preload(4);
		hwsync();
		atomic_dec(&state.s);
		hwsync();
		spin_tb(state.starttime + (state.n & jitter));
		hwsync();
		for (i = 0; i < noise_size; i++)
			fillstorebuffer[i].value++;
		THREAD_4;
		lwsync();
		atomic_dec(&state.f);
		hwsync();
	}
	return NULL;
}

#endif /* #ifdef THREAD_4 */

/*
 */
#ifdef THREAD_5

void *thread_5(void *me_in)
{
	struct cacheline fillstorebuffer[NOISE_SIZE_MAX];
	int i;
	int mycpu = (int)me_in;
	long oldtb;
	int sum = 0;

	oldtb = state.starttime;
	hwsync();
	startyourengines(mycpu);
	while (state.n < ncycles) {
		while (oldtb == state.starttime) {
			if (state.n >= ncycles)
				return NULL;
			barrier();
		}
		oldtb = state.starttime;
		preload(5);
		hwsync();
		atomic_dec(&state.s);
		hwsync();
		spin_tb(state.starttime + (state.n & jitter));
		hwsync();
		for (i = 0; i < noise_size; i++)
			fillstorebuffer[i].value++;
		THREAD_5;
		lwsync();
		atomic_dec(&state.f);
		hwsync();
	}
	return NULL;
}

#endif /* #ifdef THREAD_5 */

int validate_thread_assignment_help(void *(*t)(void *), int tn)
{
	int i = 0;

	while (thread_assignment[i].thread != NULL) {
		if (t == thread_assignment[i].thread)
			return 0;
		i++;
	}
	fprintf(stderr,
		"THREAD_%d macro defined, but thread_%d missing from "
		"thread_assignment[] array\n",
		tn, tn);
	return 1;
}

void validate_thread_assignment(void)
{
	int errcount = 0;

	errcount += validate_thread_assignment_help(thread_0, 0);
	errcount += validate_thread_assignment_help(thread_1, 1);
#ifdef THREAD_2
	errcount += validate_thread_assignment_help(thread_2, 2);
#endif /* #ifdef THREAD_2 */
#ifdef THREAD_3
	errcount += validate_thread_assignment_help(thread_3, 3);
#endif /* #ifdef THREAD_3 */
#ifdef THREAD_4
	errcount += validate_thread_assignment_help(thread_4, 4);
#endif /* #ifdef THREAD_4 */
	if (errcount > 0) {
		fprintf(stderr,
			"Aborting run, please fix thread_assignment[] array\n");
		exit(-1);
	}
}

void printstate(char *prog)
{
	long t = gettb();
	time_t tt;

	tt = time(NULL);
	printf("A = %d, A1 = %d, B = %d, C = %d, D = %d  %s",
	       state.a, state.a1, state.b, state.c, state.d,
	       ctime(&tt));
	if (state.anomalies != 0)
		printf("??? anomalies = %d (%s)\n", state.anomalies, prog);
	if (state.badcount != 0)
		printf("!!! badcount = %d (%s)\n", state.badcount, prog);
}

#define DUMP_STATE_OFFSET(f) \
	do { \
		printf("state." #f " = %d/%#x\n", \
		(long)&state.f - (long)&state, \
		(long)&state.f - (long)&state); \
	} while (0)

void dump_state_offsets(void)
{
	DUMP_STATE_OFFSET(n);
	DUMP_STATE_OFFSET(n1);
	DUMP_STATE_OFFSET(n2);

	DUMP_STATE_OFFSET(a);
	DUMP_STATE_OFFSET(a1);
	DUMP_STATE_OFFSET(a2);

	DUMP_STATE_OFFSET(b);
	DUMP_STATE_OFFSET(b1);
	DUMP_STATE_OFFSET(b2);

	DUMP_STATE_OFFSET(c);
	DUMP_STATE_OFFSET(c1);
	DUMP_STATE_OFFSET(c2);

	DUMP_STATE_OFFSET(d);
	DUMP_STATE_OFFSET(d1);
	DUMP_STATE_OFFSET(d2);

	DUMP_STATE_OFFSET(e);
	DUMP_STATE_OFFSET(e1);
	DUMP_STATE_OFFSET(e2);

	DUMP_STATE_OFFSET(v);
	DUMP_STATE_OFFSET(v1);
	DUMP_STATE_OFFSET(v2);

	DUMP_STATE_OFFSET(x);
	DUMP_STATE_OFFSET(x1);
	DUMP_STATE_OFFSET(x2);

	DUMP_STATE_OFFSET(y);
	DUMP_STATE_OFFSET(y1);
	DUMP_STATE_OFFSET(y2);

	DUMP_STATE_OFFSET(z);
	DUMP_STATE_OFFSET(z1);
	DUMP_STATE_OFFSET(z2);

	DUMP_STATE_OFFSET(starttime);
	DUMP_STATE_OFFSET(s);
	DUMP_STATE_OFFSET(f);
	DUMP_STATE_OFFSET(oldn);
	DUMP_STATE_OFFSET(anomalies);
	DUMP_STATE_OFFSET(badcount);
	DUMP_STATE_OFFSET(oldbadcount);
	DUMP_STATE_OFFSET(fillstorebuffer);
}

void usage(char *prog)
{
	fprintf(stderr,
		"Usage: %s [ --cpuoffset n ] [ --jitter n ] [ --ncycles n ] "
		    "[ --noise_size n ] [ --test_cycle_tb_mask 0xhh ] "
		    "[ --v ]\n", prog);
	exit(-1);
}

void parse_args(int argc, char *argv[])
{
	int i;

	if (argc < 2)
		return;

	for (i = 1; i < argc; i++) {
		if (strcmp("--cpuoffset", argv[i]) == 0) {
			if (++i >= argc)
				usage(argv[0]);
			cpuoffset = strtoul(argv[i], NULL, 0);
			if (cpuoffset < 0)
				cpuoffset = 0;
		} else if (strcmp("--jitter", argv[i]) == 0) {
			if (++i >= argc)
				usage(argv[0]);
			jitter = strtoul(argv[i], NULL, 0);
			if (jitter < 0)
				jitter = 0;
			else if (jitter < 0x8)
				jitter = (1 << jitter) - 1;
			else
				jitter = 0x1ff;
		} else if (strcmp("--ncycles", argv[i]) == 0) {
			if (++i >= argc)
				usage(argv[0]);
			ncycles = strtoul(argv[i], NULL, 0);
			if (ncycles < 0)
				ncycles = 1;
		} else if (strcmp("--noise_size", argv[i]) == 0) {
			if (++i >= argc)
				usage(argv[0]);
			noise_size = strtoul(argv[i], NULL, 0);
			if (noise_size < 0)
				noise_size = 2;
			if (noise_size >= NOISE_SIZE_MAX) {
				noise_size = NOISE_SIZE_MAX - 1;
			}
		} else if (strcmp("--test_cycle_tb_mask", argv[i]) == 0) {
			if (++i >= argc)
				usage(argv[0]);
			test_cycle_tb_mask = strtoul(argv[i], NULL, 0);
		} else if (strcmp("--v", argv[i]) == 0) {
			dump_config(argv[0]);
		} else if (strcmp("--vstateoffsets", argv[i]) == 0) {
			dump_state_offsets();
		} else {
			usage(argv[0]);
		}
	}
}

int main(int argc, char *argv[])
{
	int i;

	parse_args(argc, argv);

	/* validate and initialize state */

	validate_cache_layout();
	validate_thread_assignment();

	/* create threads. */

	state.starttime = gettb();
	i = 0;
	spin_lock(&threadlock);
	while (thread_assignment[i].thread != NULL) {
		num_threads_created++;
		thread_assignment[i].id = 
			create_thread(thread_assignment[i].thread,
				      (void *)(thread_assignment[i].cpu +
				      	       cpuoffset));
		i++;
	}
	spin_unlock(&threadlock);
	hwsync();
	all_threads_created = 1;

	/* Wait for threads to complete. */

	i = 0;
	while (thread_assignment[i].thread != NULL) {
		(void)wait_thread(thread_assignment[i].id);
		i++;
	}

	/* Tell the tale. */

	printstate(argv[0]);

	return (0);
}
