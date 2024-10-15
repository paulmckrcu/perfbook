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

static clockid_t clocks[] = {
	CLOCK_REALTIME,
	CLOCK_MONOTONIC,
	CLOCK_MONOTONIC_RAW,
	CLOCK_MONOTONIC_COARSE,
	CLOCK_BOOTTIME,
};
static char *clocknames[] = {
	"CLOCK_REALTIME         ",
	"CLOCK_MONOTONIC        ",
	"CLOCK_MONOTONIC_RAW    ",
	"CLOCK_MONOTONIC_COARSE ",
	"CLOCK_BOOTTIME         ",
};

static void measure_granularity(clockid_t c)
{
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
	} while (t1.tv_sec == t2.tv_nsec && t1.tv_nsec == t2.tv_nsec);
	tdiff = timespecsub(&t2, &t1);
	printf("%s granularity: %s  tries: %d\n",
	       clocknames[c], timespec2str(tdiffstr, &tdiff), i);
}

void measure_granularities(void)
{
	int c;

	for (c = 0; c < sizeof(clocks) / sizeof(clocks[0]); c++) {
		measure_granularity(c);
	}
}

static void measure_overhead(clockid_t c)
{
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
	printf("%s overhead: %g (%g) reads: %d\n",
	       clocknames[c], dt2 - dt1, dtavg, i);
}

static void measure_overheads(void)
{
	int c;

	for (c = 0; c < sizeof(clocks) / sizeof(clocks[0]); c++) {
		measure_overhead(c);
	}
}

int main(int argc, char *argv[])
{
	measure_granularities();
	printf("\n");
	measure_overheads();
	return EXIT_SUCCESS;
}
