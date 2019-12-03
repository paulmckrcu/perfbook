/*
 * lockwakelatency.c: Measure time required to unlock-wake sleeping thread
 *
 * Usage:
 * 	./lockwakelatency <nlockers> [ <duration in seconds> ]
 * 		Run a wakeup-latency test with the specified number of
 *		threads to be awakened.  Defaults to a one-second test.
 *
 * The command "./lockwakelatency 2" produces output as follows:
 *
 * n_rounds: @@@  nlockers: 2  wake latency: @@@  test duration: 1  ns/wakeup: @@@
 *
 * The "n_rounds" is the number of rounds of lock wakeup testing, the
 * "nlockers" is the number of locking threads, the "wake latency" is
 * the total time spent awakening, "test duration" is the test's wallclock
 * time, and ns/wakeup is the number of nanoseconds consumed by each
 * individual wakeup, where each round will have nlockers wakeups.
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
 * Copyright (c) 2018-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include <stdio.h>
#include <stddef.h>
#include <time.h>

#include "../api.h"

/* CLOCK_MONOTONIC_RAW prefered, but the older CLOCK_MONOTONIC will do. */
#ifdef CLOCK_MONOTONIC_RAW
#define TEST_CLOCK CLOCK_MONOTONIC_RAW
#else /* #ifdef CLOCK_MONOTONIC_RAW */
#define TEST_CLOCK CLOCK_MONOTONIC
#endif /* #else #ifdef CLOCK_MONOTONIC_RAW */

/* Get current time in free-running nanoseconds. */
unsigned long long current_time(void)
{
	struct timespec t;

	if (clock_gettime(TEST_CLOCK, &t) != 0)
		abort();
	return (unsigned long long)t.tv_sec * 1000000000ULL +
	       (unsigned long long)t.tv_nsec;
}

/*
 * Test variables.
 */

int duration = 1;
int n_rounds;
atomic_t acqctr;
atomic_t relctr;
atomic_t donectr;
unsigned long long tend;
int woke;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_RUN;

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t cond = PTHREAD_COND_INITIALIZER;
pthread_mutex_t condlock = PTHREAD_MUTEX_INITIALIZER;

/*
 * Locking wakeup latency test.
 */
void *lock_wake_latency_test(void *arg)
{
	int en;
	intptr_t me = (intptr_t)arg;

	//run_on(me);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		atomic_dec(&acqctr);
		if ((en = pthread_mutex_lock(&lock)) != 0) {
			fprintf(stderr,
				"pthread_mutex_lock: %s\n", strerror(en));
			abort();
		}
		if ((en = pthread_mutex_unlock(&lock)) != 0) {
			fprintf(stderr,
				"pthread_mutex_unlock: %s\n", strerror(en));
			abort();
		}
		if (atomic_dec_and_test(&relctr)) {
			tend = current_time();
			if ((en = pthread_mutex_lock(&condlock)) != 0) {
				fprintf(stderr,
					"pthread_mutex_lock: %s\n",
					strerror(en));
				abort();
			}
			woke = 1;
			pthread_cond_signal(&cond);
			if ((en = pthread_mutex_unlock(&condlock)) != 0) {
				fprintf(stderr,
					"pthread_mutex_unlock: %s\n",
					strerror(en));
				abort();
			}
		}
	}
	atomic_dec(&donectr);
	return (NULL);
}

void perftest(int nlockers)
{
	int en;
	intptr_t i;
	unsigned long long t;
	unsigned long long tdelta;
	unsigned long long tstart;
	unsigned long long ttot;

	atomic_set(&acqctr, nlockers);
	atomic_set(&relctr, nlockers);
	atomic_set(&donectr, nlockers);
	for (i = 0; i < nlockers; i++)
		create_thread(lock_wake_latency_test, (void *)i);
	//run_on(i);
	while (atomic_read(&acqctr) > 0)
		poll(NULL, 0, 1);
	smp_mb();
	WRITE_ONCE(goflag, GOFLAG_RUN);
	tstart = current_time();
	do {
		if ((en = pthread_mutex_lock(&lock)) != 0) {
			fprintf(stderr,
				"pthread_mutex_lock: %s\n", strerror(en));
			perror("perftest:pthread_mutex_lock");
			abort();
		}
		smp_mb();
		while (atomic_read(&acqctr) > 0)
			poll(NULL, 0, 1);
		smp_mb();
		atomic_set(&acqctr, nlockers);
		atomic_set(&relctr, nlockers);
		woke = 0;
		poll(NULL, 0, 10);
		t = current_time();
		smp_mb();
		if ((en = pthread_mutex_unlock(&lock)) != 0) {
			fprintf(stderr,
				"pthread_mutex_unlock: %s\n", strerror(en));
			abort();
		}
		if ((en = pthread_mutex_lock(&condlock)) != 0) {
			fprintf(stderr,
				"pthread_mutex_lock: %s\n", strerror(en));
			abort();
		}
		if (atomic_read(&relctr) > 0 || !woke)
			pthread_cond_wait(&cond, &condlock);
		if ((en = pthread_mutex_unlock(&condlock)) != 0) {
			fprintf(stderr,
				"pthread_mutex_unlock: %s\n", strerror(en));
			abort();
		}
		smp_mb();
		tdelta = tend - t;
		ttot += tdelta;
		//printf("delta = %lld ns\n", tdelta);
		n_rounds++;
	} while (tstart + duration * 1000000000ULL > t);
	WRITE_ONCE(goflag, GOFLAG_STOP);
	while (atomic_read(&donectr) > 0)
		poll(NULL, 0, 1);
	printf("n_rounds: %d  nlockers: %d  wake latency: %g  test duration: %d  ns/wakeup %lld\n",
	       n_rounds, nlockers, (double)ttot / 1000000000., duration, ttot / n_rounds / nlockers);
	exit(EXIT_SUCCESS);
}


/*
 * Mainprogram.
 */

int main(int argc, char *argv[])
{
	int nlockers = 0;

	smp_init();

	if (argc > 1) {
		nlockers = strtoul(argv[1], NULL, 0);
		if (argc == 3)
			duration = strtoul(argv[2], NULL, 0);
		if (argc <= 3)
			perftest(nlockers);
	}
	fprintf(stderr, "Usage: %s nlockers [ duration (s) ]\n", argv[0]);
	exit(EXIT_FAILURE);
}
