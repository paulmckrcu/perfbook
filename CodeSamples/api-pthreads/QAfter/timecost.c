/*
 * Measure the overhead of several clock_gettime() options.
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
 * Copyright (c) 2024 Paul E. McKenney, Meta Platforms, Inc.
 */

#include "../util.h"
#include "timespec.h"

#ifdef __x86_64__

// Taken from Linux kernel v6.11.
#define DECLARE_ARGS(val, low, high)	unsigned long low, high
#define EAX_EDX_VAL(val, low, high)	((low) | (high) << 32)
#define EAX_EDX_RET(val, low, high)	"=a" (low), "=d" (high)

static __always_inline unsigned long long rdtsc(void)
{
	DECLARE_ARGS(val, low, high);

	asm volatile("rdtsc" : EAX_EDX_RET(val, low, high));

	return EAX_EDX_VAL(val, low, high);
}

static void measure_overhead_arch(void)
{
	double dt1;
	double dt2;
	double dtavg;
	int i;
	int retval;
	unsigned long long t1;

	dt1 = dgettimeofday();
	for (i = 0; i < 1000 * 1000; i++)
		t1 = rdtsc();
	dt2 = dgettimeofday();
	dtavg = (dt2 - dt1) / i;
	printf("x86_64 rdtsc              overhead: %g (%g) reads: %d\n",
	       dt2 - dt1, dtavg, i);
}

#else

static void measure_overhead_arch(void)
{
	printf("Architecture unsupported.\n");
}

#endif

static clockid_t clocks[] = {
	CLOCK_REALTIME,
	CLOCK_REALTIME_COARSE,
	CLOCK_MONOTONIC,
	CLOCK_MONOTONIC_RAW,
	CLOCK_MONOTONIC_COARSE,
	CLOCK_BOOTTIME,
};
static char *clocknames[] = {
	"CLOCK_REALTIME         ",
	"CLOCK_REALTIME_COARSE  ",
	"CLOCK_MONOTONIC        ",
	"CLOCK_MONOTONIC_RAW    ",
	"CLOCK_MONOTONIC_COARSE ",
	"CLOCK_BOOTTIME         ",
};

static void measure_granularity(int cidx)
{
	clockid_t c = clocks[cidx];
	int i = 0;
	int retval;
	struct timespec t1;
	struct timespec t2;
	struct timespec tdiff;
	char tdiffstr[32];

	retval = clock_gettime(c, &t1);
	assert(!retval);
	do {
		retval = clock_gettime(c, &t2);
		assert(!retval);
		i++;
	} while (t1.tv_sec == t2.tv_sec && t1.tv_nsec == t2.tv_nsec);
	tdiff = timespecsub(&t2, &t1);
	printf("%d %s granularity: %ld.%09ld  tries: %d\n",
	       c, clocknames[cidx], tdiff.tv_sec, tdiff.tv_nsec, i);
	// printf("\tt1: %ld.%09ld t2: %ld.%09ld\n",
	//        t1.tv_sec, t1.tv_nsec, t2.tv_sec, t2.tv_nsec);
}

void measure_granularities(void)
{
	int c;

	for (c = 0; c < sizeof(clocks) / sizeof(clocks[0]); c++) {
		measure_granularity(c);
	}
}

static void measure_overhead(int cidx)
{
	clockid_t c = clocks[cidx];
	double dt1;
	double dt2;
	double dtavg;
	int i;
	int retval;
	struct timespec t1;

	dt1 = dgettimeofday();
	for (i = 0; i < 1000 * 1000; i++) {
		retval = clock_gettime(c, &t1);
		assert(!retval);
	}
	dt2 = dgettimeofday();
	dtavg = (dt2 - dt1) / i;
	printf("%d %s overhead: %g (%g) reads: %d\n",
	       c, clocknames[cidx], dt2 - dt1, dtavg, i);
}

static void measure_overheads(void)
{
	int c;

	for (c = 0; c < sizeof(clocks) / sizeof(clocks[0]); c++) {
		measure_overhead(c);
		poll(NULL, 0, 15 * 1000); // Let the chip cool down
	}
	measure_overhead_arch();
}

int main(int argc, char *argv[])
{
	measure_granularities();
	printf("\n");
	measure_overheads();
	return EXIT_SUCCESS;
}
