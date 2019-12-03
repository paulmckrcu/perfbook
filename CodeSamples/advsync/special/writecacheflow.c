/*
 * Program to do fine-grained timing of cached writes on POWER,
 * including information allowing mapping of the data flow.
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
 * Copyright (C) IBM Corporation, 2005-2019
 * Copyright (C) Facebook, 2019
 *
 * Authors: Paul E. McKenney <paulmck@us.ibm.com>
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
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
long nrecorders = 1;
long test_cycle_tb_mask	= 0xff;		/* These TB bits 0: start rep */

/*
 * Architectural constants.
 */

#define CACHE_LINE_SIZE		128
#define NOISE_SIZE		8
#define MAX_CPUS		32

/*
 * Memory barriers and atomic instructions.
 */

#define barrier() __asm__ __volatile__ ("" : : : "memory")
#define hwsync() __asm__ __volatile__ ("sync" : : : "memory")
#define isync() __asm__ __volatile__ ("isync" : : : "memory")
#define lwsync() __asm__ __volatile__ ("lwsync" : : : "memory")

/*
 * Dump the configuration, abort if ill-formed.
 * Though if ill-formed, probably couldn't compile anyway...
 */
void dump_config(void)
{
	int error = 0;

	printf("CPU offset: %ld\n", cpuoffset);
	printf("Cache-line size: %d bytes\n", CACHE_LINE_SIZE);
	printf("Store-buffer noise size: %d cache lines\n", NOISE_SIZE);
	printf("Maximum number of CPUs: %d\n", MAX_CPUS);
	printf("Start each rep when these bits of TB are zero: %lx\n",
	       test_cycle_tb_mask);
	if ((test_cycle_tb_mask & (test_cycle_tb_mask + 1)) != 0) {
		printf("test_cycle_tb_mask must be consecutive low-order bits"
		       " (e.g., 0xff)\n");
		error = 1;
	}
	printf("Number of recorders: %ld\n", nrecorders);
	fflush(stdout);
	if (error != 0)
		exit(EXIT_FAILURE);
}

/*
 * Return the lower 32 bits of the time-base register.
 */
static __inline__ long gettb(void)
{
	long t;

	__asm__ __volatile__("mftb %0" : "=&r" (t) : : "memory");
	return t;
}

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
 * Data for measurement.
 */

struct ctxt_state {
	double	aalign;
	char	afill[CACHE_LINE_SIZE];
	long	starttime;	/* timestamp counter value to start at. */
	char	sfill[CACHE_LINE_SIZE - sizeof(long)];
	long	variable;	/* variable being stored to. */
	char	vfill[CACHE_LINE_SIZE - sizeof(long)];
	char	noise[CACHE_LINE_SIZE * NOISE_SIZE];
} state = { 0 };

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
	int en;

	if ((en = pthread_mutex_lock(lp)) != 0) {
		fprintf(stderr, "pthread_mutex_lock: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
}

void spin_unlock(pthread_mutex_t *lp)
{
	int en;

	if ((en = pthread_mutex_unlock(lp)) != 0) {
		fprintf(stderr, "pthread_mutex_unlock: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
}

pthread_t create_thread(void *(*func)(void *), void *arg)
{
	int en;
	pthread_t id;

	if ((en = pthread_create(&id, NULL, func, arg)) != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	return id;
}

void *wait_thread(pthread_t id)
{
	int en;
	void *retval;

	if ((en = pthread_join(id, &retval)) != 0) {
		fprintf(stderr, "pthread_join: %s\n", strerror(en));
		exit(EXIT_FAILURE);
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
		exit(EXIT_FAILURE);
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

/*
 * This function runs on CPU 0, and is responsible for setting
 * the start time, and then waiting a decent interval for all
 * caches to agree on the new value.
 */

void setstarttime(void *me_in)
{
	long mycpu = (long)me_in;

	startyourengines(mycpu);
	hwsync();
	state.starttime = next_test_cycle_start();
	hwsync();
	return;
}

struct valuerange {
	long firsttb;
	int value;
	long lasttb;
};

/*
 * This function runs on the remaining CPUs, each storing its ID into
 * state.variable and recording its history.
 */

void *recorder(void *me_in)
{
	int curvalue;
	long firsttb;
	int i;
	int j;
	long lasttb;
	long mycpu = (long)me_in;
	long oldtb;
	struct valuerange vr[MAX_CPUS];

	oldtb = state.starttime;
	curvalue = mycpu;
	hwsync();
	startyourengines(mycpu);
	while (oldtb == state.starttime)
		barrier();
	hwsync();
	spin_tb(state.starttime);
	for (i = 0; i < NOISE_SIZE; i++)
		state.noise[i * CACHE_LINE_SIZE] = mycpu;
	state.variable = mycpu;
	for (i = 0; i < MAX_CPUS; i++) {
		lasttb = oldtb = firsttb = gettb();
		while (state.variable == curvalue) {
			lasttb = oldtb;
			oldtb = gettb();
			if (lasttb - firsttb > 1000)
				goto timeout;
		}
		vr[i].firsttb = firsttb;
		vr[i].value = curvalue;
		vr[i].lasttb = lasttb;
		curvalue = state.variable;
	}
timeout:
	vr[i].firsttb = firsttb;
	vr[i].value = curvalue;
	vr[i].lasttb = lasttb;
	spin_lock(&threadlock);
	for (j = 0; j <= i; j++)
		printf("%2ld %2d: %ld - %ld = %ld\n",
		       mycpu,
		       vr[j].value,
		       vr[j].firsttb - state.starttime,
		       vr[j].lasttb - state.starttime,
		       vr[j].lasttb - vr[j].firsttb);
	spin_unlock(&threadlock);
	return NULL;
}

void usage(char *prog)
{
	fprintf(stderr,
		"Usage: %s [ --cpuoffset n ] [ --nrecorders n ] "
		    "[ --test_cycle_tb_mask 0xhh ] [ --v ]\n", prog);
	exit(EXIT_FAILURE);
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
		} else if (strcmp("--nrecorders", argv[i]) == 0) {
			if (++i >= argc)
				usage(argv[0]);
			nrecorders = strtoul(argv[i], NULL, 0);
			if (nrecorders < 0)
				nrecorders = 2;
			if (nrecorders >= MAX_CPUS) {
				nrecorders = MAX_CPUS - 1;
			}
		} else if (strcmp("--test_cycle_tb_mask", argv[i]) == 0) {
			if (++i >= argc)
				usage(argv[0]);
			test_cycle_tb_mask = strtoul(argv[i], NULL, 0);
		} else if (strcmp("--v", argv[i]) == 0) {
			dump_config();
		} else {
			usage(argv[0]);
		}
	}
}

int main(int argc, char *argv[])
{
	int i;
	pthread_t *recorder_id;

	parse_args(argc, argv);

	/* create threads. */

	runon(0);
	num_threads_created++;
	state.starttime = gettb();
	state.variable = -1;
	recorder_id = (pthread_t *)malloc(nrecorders *
					  sizeof(*recorder_id));
	if (recorder_id == NULL) {
		fprintf(stderr, "Out of memory!\n");
		exit(EXIT_FAILURE);
	}
	for (i = 0; i < nrecorders; i++) {
		num_threads_created++;
		recorder_id[i] = create_thread(recorder,
					       (void *)(1 + i + cpuoffset));
	}
	hwsync();
	all_threads_created = 1;
	setstarttime(0);

	/* Wait for threads to complete. */

	poll(NULL, 0, 1);
	for (i = 0; i < nrecorders; i++) {
		(void)wait_thread(recorder_id[i]);
	}

	return EXIT_SUCCESS;
}
