/*
 * Measure the overhead of several clock_gettime() options.
 *
 * Sample output:
 *
 * 0 CLOCK_REALTIME          granularity: 0.000000432  tries: 1
 * 5 CLOCK_REALTIME_COARSE   granularity: 0.001000008  tries: 25933
 * 1 CLOCK_MONOTONIC         granularity: 0.000000164  tries: 1
 * 4 CLOCK_MONOTONIC_RAW     granularity: 0.000000140  tries: 1
 * 6 CLOCK_MONOTONIC_COARSE  granularity: 0.001000009  tries: 38983
 * 7 CLOCK_BOOTTIME          granularity: 0.000000087  tries: 1
 *
 * 0 CLOCK_REALTIME          7.69e-08 s (2.00e-08 -> 1.23e-07) reads: 100000
 * 5 CLOCK_REALTIME_COARSE   2.45e-08 s (2.44e-08 -> 5.61e-08) reads: 100000
 * 1 CLOCK_MONOTONIC         7.69e-08 s (7.69e-08 -> 1.08e-07) reads: 100000
 * 4 CLOCK_MONOTONIC_RAW     7.89e-08 s (1.84e-08 -> 1.13e-07) reads: 100000
 * 6 CLOCK_MONOTONIC_COARSE  2.45e-08 s (6.31e-09 -> 5.23e-08) reads: 100000
 * 7 CLOCK_BOOTTIME          7.70e-08 s (2.46e-08 -> 1.12e-07) reads: 100000
 * x86_64 rdtsc              3.17e-08 s (8.15e-09 -> 5.42e-08) reads: 100000
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

#include <stdarg.h>
#include "../util.h"
#include "../include/timespec.h"

#define NSAMPLES 100
#define NSUBSAMPLES 1000
#define COOLDOWN 5

int nsamples = NSAMPLES;
int nsubsamples = NSUBSAMPLES;
int cooldown = COOLDOWN;

// Helper function for qsort().
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

// Extract minimum, median, and maximum from the specified array.
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

// Collect measurements of the architure-specific timebase.
static void measure_overhead_arch(void)
{
	double dtdiff;
	double dtmax;
	double dtmed;
	double dtmin;
	double *dts;
	int i;
	int j;
	const int ns = nsamples;
	const int nss = nsubsamples;
	int retval;
	unsigned long long t1;
	struct timespec ts1;
	struct timespec ts2;

	dts = malloc(sizeof(*dts) * nsamples);
	for (i = 0; i < ns; i++) {
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
	free(dts);
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

// Measure time required for the specified clocksource to tick.
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

// Measure times required for each clocksource to tick.
void measure_granularities(void)
{
	int c;

	for (c = 0; c < sizeof(clocks) / sizeof(clocks[0]); c++) {
		measure_granularity(c);
	}
}

// Measure the access overhead of the specified clocksource.
static void measure_overhead(int cidx)
{
	clockid_t c = clocks[cidx];
	double dtdiff;
	double dtmax;
	double dtmed;
	double dtmin;
	double *dts;
	int i;
	int j;
	const int ns = nsamples;
	const int nss = nsubsamples;
	int retval;
	struct timespec t1;
	struct timespec ts1;
	struct timespec ts2;

	dts = malloc(sizeof(*dts) * nsamples);
	for (i = 0; i < ns; i++) {
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
		poll(NULL, 0, cooldown);  // Let the chip cool down.
	}
	getstats(dts, i, &dtmin, &dtmed, &dtmax);
	printf("%d %s %#8.3g s (%#8.3g -> %#8.3g) reads: %d\n",
	       c, clocknames[cidx], dtmed, dtmin, dtmax, i * j);
	free(dts);
}

// Measure the access overheads of each clocksource.
static void measure_overheads(void)
{
	int c;

	poll(NULL, 0, cooldown);
	for (c = 0; c < sizeof(clocks) / sizeof(clocks[0]); c++) {
		measure_overhead(c);
	}
	measure_overhead_arch();
}

void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "Usage: %s\n", progname);
	fprintf(stderr, "\t--cooldown\n");
	fprintf(stderr, "\t\tCooldown period between tests in milliseconds.\n");
	fprintf(stderr, "\t\tDefaults to %d.\n", COOLDOWN);
	fprintf(stderr, "\t--nsamples\n");
	fprintf(stderr, "\t\tNumber of per-clocksource samples to take.\n");
	fprintf(stderr, "\t\tDefaults to %d.\n", NSAMPLES);
	fprintf(stderr, "\t--nsubsamples\n");
	fprintf(stderr, "\t\tNumber of measurements per sample.\n");
	fprintf(stderr, "\t\tMaking this too large defeats --cooldown.\n");
	fprintf(stderr, "\t\tDefaults to %d.\n", NSUBSAMPLES);
	exit(-1);
}

int main(int argc, char *argv[])
{
	int i = 1;

	while (i < argc) {
		if (strcmp(argv[i], "--cooldown") == 0) {
			cooldown = atoi(argv[++i]);
			if (cooldown < 0)
				usage(argv[0], "%s must be > 0\n",
				      argv[ i - 1]);
		} else if (strcmp(argv[i], "--nsamples") == 0) {
			nsamples = atoi(argv[++i]);
			if (nsamples < 1)
				usage(argv[0], "%s must be >= 0\n",
				      argv[ i - 1]);
		} else if (strcmp(argv[i], "--nsubsamples") == 0) {
			nsubsamples = atoi(argv[++i]);
			if (nsubsamples < 1)
				usage(argv[0], "%s must be >= 0\n",
				      argv[ i - 1]);
		} else {
			usage(argv[0], "Unrecognized argument: %s\n", argv[i]);
		}
		i++;
	}
	measure_granularities();
	printf("\n");
	measure_overheads();
	return EXIT_SUCCESS;
}
