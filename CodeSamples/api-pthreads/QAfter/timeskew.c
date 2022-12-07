/*
 * Time-skew demo.
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

#include "../util.h"
#include <time.h>
#include <stdarg.h>

int interval = 100;		// Milliseconds.
int nsamples = 20;

struct timespec *mono;		// Monotonic time.
struct timespec *wc;		// Wall-clock ("real") time.

static double timespec2double(struct timespec *tsp)
{
	return tsp->tv_sec + (double)tsp->tv_nsec / 1000. / 1000. / 1000.;
}

void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "Usage: %s\n", progname);
	fprintf(stderr, "\t--interval\n");
	fprintf(stderr, "\t\tInterval between samples in milliseconds.\n");
	fprintf(stderr, "\t\tDefaults to 100\n");
	fprintf(stderr, "\t--nsamples\n");
	fprintf(stderr, "\t\tNumber of time-skew samples to taek.\n");
	fprintf(stderr, "\t\tDefaults to 20\n");
	exit(-1);
}

int main(int argc, char *argv[])
{
	int i = 1;
	double monobase;
	double monocur;
	double wcbase;
	double wccur;

	while (i < argc) {
		if (strcmp(argv[i], "--interval") == 0) {
			interval = atoi(argv[++i]);
			if (interval < 1)
				usage(argv[0], "%s must be >= 0\n",
				      argv[ i - 1]);
		} else if (strcmp(argv[i], "--nsamples") == 0) {
			nsamples = atoi(argv[++i]);
			if (nsamples < 1)
				usage(argv[0], "%s must be >= 0\n",
				      argv[ i - 1]);
		} else {
			usage(argv[0], "Unrecognized argument: %s\n", argv[i]);
		}
		i++;
	}
	mono = malloc(nsamples * sizeof(*mono));
	wc = malloc(nsamples * sizeof(*wc));
	if (!mono || !wc) {
		fprintf(stderr, "Out of memory!\n");
		exit(1);
	}
	for (i = 0; i < nsamples; i++) {
		if (clock_gettime(CLOCK_MONOTONIC, &mono[i])) {
			perror("clock_gettime(CLOCK_MONOTONIC)");
			exit(2);
		}
		if (clock_gettime(CLOCK_REALTIME, &wc[i])) {
			perror("clock_gettime(CLOCK_REALTIME)");
			exit(3);
		}
		poll(NULL, 0, interval);
	}
	monobase = timespec2double(&mono[0]);
	wcbase = timespec2double(&wc[0]);
	for (i = 0; i < nsamples; i++) {
		monocur = timespec2double(&mono[i]) - monobase;
		wccur = timespec2double(&wc[i]) - wcbase;
		printf("%.10g %.10g %g\n", monocur, wccur, monocur - wccur);
	}

	return EXIT_SUCCESS;
}
