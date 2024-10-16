/*
 * Helper functions for timespec manipulation.
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

#ifndef _TIMESPEC_H_
#define _TIMESPEC_H_

#include <assert.h>

static inline int timespeccmp(struct timespec *tsp1, struct timespec *tsp2)
{
	if (tsp1->tv_sec < tsp2->tv_sec ||
	    (tsp1->tv_sec == tsp2->tv_sec && tsp1->tv_nsec < tsp2->tv_nsec))
		return -1;
	if (tsp1->tv_sec == tsp2->tv_sec && tsp1->tv_sec == tsp2->tv_sec)
		return 0;
	return 1;
}

// Convert a single timespec to double precision.
static inline double timespec2double(struct timespec *tsp)
{
	return tsp->tv_sec + (double)tsp->tv_nsec / 1000. / 1000. / 1000.;
}

// Compute the difference of a pair of timespec structures, *tsp1 - *tsp2.
static inline struct timespec timespecsub(struct timespec *tsp1, struct timespec *tsp2)
{
	struct timespec tsdiff = {};

	assert(tsdiff.tv_nsec == 0 && tsdiff.tv_sec == 0);
	if (tsp1->tv_sec < tsp2->tv_sec ||
	    (tsp1->tv_sec == tsp2->tv_sec && tsp1->tv_nsec < tsp2->tv_nsec)) {
		tsdiff = timespecsub(tsp2, tsp1);
		tsdiff.tv_sec = -tsdiff.tv_sec;
		tsdiff.tv_nsec = -tsdiff.tv_nsec;
		return tsdiff;
	}
	tsdiff.tv_nsec = tsp1->tv_nsec - tsp2->tv_nsec;
	if (tsdiff.tv_nsec < 0) {
		tsdiff.tv_nsec += 1000. * 1000. * 1000.;
		tsdiff.tv_sec--;
	}
	tsdiff.tv_sec += tsp1->tv_sec - tsp2->tv_sec;
	return tsdiff;
}

// Convert (*tsp1 - *tsp2) to double precision (decimal seconds).
static inline double timespecs2double(struct timespec *tsp1, struct timespec *tsp2)
{
	struct timespec tsdiff;

	tsdiff = timespecsub(tsp1, tsp2);
	return tsdiff.tv_sec + (double)tsdiff.tv_nsec / 1000. / 1000. / 1000.;
}

static inline char *timespec2str(char *cp, struct timespec *tsp)
{
	sprintf(cp, "%ld.%09ld",
		tsp->tv_sec, tsp->tv_nsec >= 0 ? tsp->tv_nsec : -tsp->tv_nsec);
	return cp;
}

#endif //  _TIMESPEC_H_
