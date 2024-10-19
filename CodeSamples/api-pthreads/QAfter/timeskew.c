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
#include <assert.h>

int interval = 100;		// Milliseconds.
int nsamples = 20;

struct timespec *mono;		// Monotonic time.
struct timespec *mono1;		// Monotonic time, first re-read (after wc).
struct timespec *mono2;		// Monotonic time, second re-read.
struct timespec *wc;		// Wall-clock ("real") time.

#include "../include/timespec.h"

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
	fprintf(stderr, "\t\tNumber of time-skew samples to take.\n");
	fprintf(stderr, "\t\tDefaults to 20\n");
	exit(-1);
}

int main(int argc, char *argv[])
{
	int i = 1;
	double monocur;
	double mono1cur;
	double mono2cur;
	char monostr[32];
	char mono1str[32];
	char mono2str[32];
	double wccur;
	char wcstr[32];

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
	mono1 = malloc(nsamples * sizeof(*mono1));
	mono2 = malloc(nsamples * sizeof(*mono2));
	wc = malloc(nsamples * sizeof(*wc));
	if (!mono ||!mono1 ||  !mono2 || !wc) {
		fprintf(stderr, "Out of memory!\n");
		exit(1);
	}

	// Collect the timestamp samples.
	for (i = 0; i < nsamples; i++) {
		if (clock_gettime(CLOCK_MONOTONIC, &mono[i])) {
			perror("clock_gettime(CLOCK_MONOTONIC)");
			exit(2);
		}
		if (clock_gettime(CLOCK_REALTIME, &wc[i])) {
			perror("clock_gettime(CLOCK_REALTIME)");
			exit(3);
		}
		if (clock_gettime(CLOCK_MONOTONIC, &mono1[i])) {
			perror("clock_gettime(CLOCK_MONOTONIC) re-read 1");
			exit(4);
		}
		if (clock_gettime(CLOCK_MONOTONIC, &mono2[i])) {
			perror("clock_gettime(CLOCK_MONOTONIC) re-read 2");
			exit(5);
		}
		if (timespeccmp(&mono2[i], &mono1[i]) < 0)
			printf("Backwards time: %s -> %s\n",
			       timespec2str(mono1str, &mono1[i]),
			       timespec2str(mono2str, &mono2[i]));
		poll(NULL, 0, interval);
	}

	// Normalize based on the respective start times.
	for (i = nsamples - 1; i >= 0; i--) {
		struct timespec oldmono1;
		struct timespec oldmono2;
		char oldmono1str[32];
		char oldmono2str[32];

		oldmono1 = mono1[i];
		mono1[i] = timespecsub(&mono1[i], &mono[0]);
		oldmono2 = mono2[i];
		mono2[i] = timespecsub(&mono2[i], &mono[0]);
		wc[i] = timespecsub(&wc[i], &wc[0]);
		mono[i] = timespecsub(&mono[i], &mono[0]);
		if (timespeccmp(&mono2[i], &mono1[i]) < 0)
			printf("Backwards time: From %s -> %s to %s -> %s\n",
			       timespec2str(oldmono1str, &oldmono1),
			       timespec2str(oldmono2str, &oldmono2),
			       timespec2str(mono1str, &mono1[i]),
			       timespec2str(mono2str, &mono2[i]));
	}

	// Output the differences.
	for (i = 0; i < nsamples; i++) {
		monocur = timespec2double(&mono[i]);
		wccur = timespec2double(&wc[i]);
		mono1cur = timespec2double(&mono1[i]);
		mono2cur = timespec2double(&mono2[i]);
		printf("%s %s %s %s %.3g %.3g %.3g\n",
		       timespec2str(monostr, &mono[i]),
		       timespec2str(wcstr, &wc[i]),
		       timespec2str(mono1str, &mono1[i]),
		       timespec2str(mono2str, &mono2[i]),
		       wccur - monocur,
		       mono1cur - monocur, // mono+wc overhead
		       mono2cur - mono1cur); // mono overhead
	}

	return EXIT_SUCCESS;
}
