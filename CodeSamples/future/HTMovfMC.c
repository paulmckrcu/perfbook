/*
 * HTMovfMC.c: Monte Carlo computation of cache-overflow probability
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
 * Copyright (c) 2012-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/* CLOCK_MONOTONIC_RAW prefered, but the older CLOCK_MONOTONIC will do. */
#ifdef CLOCK_MONOTONIC_RAW
#define HTM_CLOCK CLOCK_MONOTONIC_RAW
#else /* #ifdef CLOCK_MONOTONIC_RAW */
#define HTM_CLOCK CLOCK_MONOTONIC
#endif /* #else #ifdef CLOCK_MONOTONIC_RAW */

/* Get current time in free-running nanoseconds. */
unsigned long long current_time(void)
{
	struct timespec t;

	if (clock_gettime(HTM_CLOCK, &t) != 0)
		abort();
	return (unsigned long long)t.tv_sec * 1000000000ULL +
	       (unsigned long long)t.tv_nsec;
}

void usage(char *argv[])
{
	fprintf(stderr, "Usage: %s nsets assoc nrefs reps\n", argv[0]);
	exit(-1);
}

int main(int argc, char *argv[])
{
	int assoc;	/* Cache associativity. */
	unsigned long long currep;
	int i;
	int nrefs;	/* Number of references. */
	int nsets;	/* Cache sets.  # cache lines is assoc*nsets. */
	unsigned long long ovf;
	unsigned long long reps;
	unsigned long long *s;

	if (argc != 5) {
		usage(argv);
	}
	nsets = atoi(argv[1]);
	assoc = atoi(argv[2]);
	nrefs = atoi(argv[3]);
	reps = strtoull(argv[4], NULL, 0);
	srandom(current_time());
	s = malloc(nsets * sizeof(s[0]));
	if (s == NULL)
		abort();

	ovf = 0;
	for (currep = 0; currep < reps; currep++) {
		for (i = 0; i < nsets; i++)
			s[i] = 0;
		for (i = 0; i < nrefs; i++) {
			s[(random() / 81) % nsets]++;
		}
		for (i = 0; i < nsets; i++)
			if (s[i] > assoc) {
				ovf++;
				break;
			}
	}
	printf("print(\"@@@ p(success) = \", bfloat(%llu/%llu));\n",
	       ovf, reps);
	exit(0);
}
