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
#include "../include/timespec.h"

#define NSAMPLES 100
#define NSUBSAMPLES 1000
#define COOLDOWN 5

int nsubsamples = NSUBSAMPLES;
int cooldown = COOLDOWN;

int dblcmp(const void *a_in, const void *b_in)
{
	double a = *(double *)a_in;
	double b = *(double *)b_in;

	if (a > b)
		return 1;
	if (b < a)
		return -1;
	return 0;
}

void getstats(double *x, int xn, double *dtmin, double *dtmed, double *dtmax)
{
	int i;

	if (xn <= 0) {
		*dtmin = *dtmed = *dtmax = 0.0;
		return;
	}
	qsort(x, xn, sizeof(x[0]), dblcmp);
	if (xn & 0x1)
		*dtmed = x[xn / 2];
	else
		*dtmed = (x[xn / 2] + x[xn / 2 - 1]) / 2.0;
	*dtmin = x[0];
	*dtmax = x[xn - 1];
}

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
	double dtdiff;
	double dtmax;
	double dtmed;
	double dtmin;
	double dts[NSAMPLES];
	int i;
	int j;
	const int nss = nsubsamples;
	int retval;
	unsigned long long t1;
	struct timespec ts1;
	struct timespec ts2;

	for (i = 0; i < sizeof(dts) / sizeof(dts[0]); i++) {
		retval = clock_gettime(CLOCK_BOOTTIME, &ts1);
		assert(!retval);
		for (j = 0; j < nss; j++)
			t1 = rdtsc();
		retval = clock_gettime(CLOCK_BOOTTIME, &ts2);
		assert(!retval);
		dtdiff = timespecs2double(&ts2, &ts1);
		dts[i] = dtdiff / (double)j;
		poll(NULL, 0, cooldown);
	}
	getstats(dts, i, &dtmin, &dtmed, &dtmax);
	printf("x86_64 rdtsc              %#8.3g s (%#8.3g -> %#8.3g) reads: %d\n",
	       dtmed, dtmin, dtmax, i * j);
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
#ifdef CLOCK_NON_MONOTONIC
	CLOCK_NON_MONOTONIC,
#endif
	CLOCK_BOOTTIME,
};
static char *clocknames[] = {
	"CLOCK_REALTIME         ",
	"CLOCK_REALTIME_COARSE  ",
	"CLOCK_MONOTONIC        ",
	"CLOCK_MONOTONIC_RAW    ",
	"CLOCK_MONOTONIC_COARSE ",
#ifdef CLOCK_NON_MONOTONIC
	"CLOCK_NON_MONOTONIC    ",
#endif
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
	double dtdiff;
	double dtmax;
	double dtmed;
	double dtmin;
	double dts[NSAMPLES];
	int i;
	int j;
	const int nss = nsubsamples;
	int retval;
	struct timespec t1;
	struct timespec ts1;
	struct timespec ts2;

	for (i = 0; i < sizeof(dts) / sizeof(dts[0]); i++) {
		retval = clock_gettime(CLOCK_BOOTTIME, &ts1);
		assert(!retval);
		for (j = 0; j < nss; j++) {
			retval = clock_gettime(c, &t1);
			assert(!retval);
		}
		retval = clock_gettime(CLOCK_BOOTTIME, &ts2);
		assert(!retval);
		dtdiff = timespecs2double(&ts2, &ts1);
		dts[i] = dtdiff / (double)j;
		poll(NULL, 0, cooldown);
	}
	getstats(dts, i, &dtmin, &dtmed, &dtmax);
	printf("%d %s %#8.3g s (%#8.3g -> %#8.3g) reads: %d\n",
	       c, clocknames[cidx], dtmed, dtmin, dtmax, i * j);
}

static void measure_overheads(void)
{
	int c;

	poll(NULL, 0, cooldown);
	for (c = 0; c < sizeof(clocks) / sizeof(clocks[0]); c++) {
		measure_overhead(c);
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
