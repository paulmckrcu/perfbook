/*
 * tscalibrate.c: Calibrate the get_timestamp() function
 *
 * This test produces output similar to the following:
 *
 * duration: 100 maxlatency: 5 nsamples: 24 min: 0.416666 max: 0.416674 avg: 0.41667 (ns per timestamp unit)
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
 * Copyright (c) 2023 Paul E. McKenney, Meta Platforms Inc.
 */

#include "../api.h"
#include <time.h>
#include <stdarg.h>
#include <stdbool.h>

struct sample {
	long long s_cgtdur;
	long long s_tsdur;
};

/*
 * Test variables.
 */

static int duration = 100;
static int maxlatency = 5;
static int nsamples = 24;

// Collect one timestamp.
bool ts1read(struct sample *sp)
{
	long long cgt1;
	long long cgt2;

	cgt1 = get_microseconds();
	sp->s_tsdur = get_timestamp();
	cgt2 = get_microseconds();
	if (cgt2 < cgt1 || cgt2 - cgt1 > maxlatency)
		return false;
	sp->s_cgtdur = (cgt1 + cgt2) / 2ULL;
	return true;
}

// Collect one timestamp calibration sample.
void ts1sample(struct sample *sp)
{
	int i = 0;
	struct sample s1;
	struct sample s2;

	for (;;) {
		BUG_ON(++i > 10);
		if (!ts1read(&s1))
			continue;
		poll(NULL, 0, duration);
		if (ts1read(&s2))
			break;
	}
	sp->s_cgtdur = s2.s_cgtdur - s1.s_cgtdur;
	sp->s_tsdur = s2.s_tsdur - s1.s_tsdur;
}

// Collect timestamp calibration samples.
void tscollectsamples(struct sample *sp)
{
	int i;

	for (i = 0; i < nsamples; i++)
		ts1sample(&sp[i]);
}

// Collect the samples, compute the statistics, and print the results.
void tscalibrate(void)
{
	double avg_cgt;
	double avg_ts;
	double cur;
	int i;
	double max;
	double min;
	struct sample *sp = calloc(nsamples, sizeof(*sp));
	struct sample sum = {};

	BUG_ON(!sp);
	tscollectsamples(sp);

	sum = sp[0];
	min = sp[0].s_cgtdur * 1000. / (double)sp[0].s_tsdur;
	max = sp[0].s_cgtdur * 1000. / (double)sp[0].s_tsdur;
	for (i = 1; i < nsamples; i++) {
		sum.s_cgtdur += sp[i].s_cgtdur;
		sum.s_tsdur += sp[i].s_tsdur;
		cur = sp[i].s_cgtdur * 1000. / (double)sp[i].s_tsdur;
		if (cur < min)
			min = cur;
		if (cur > max)
			max = cur;
	}
	avg_cgt = sum.s_cgtdur / (double)nsamples;
	avg_ts = sum.s_tsdur / (double)nsamples;
	printf("duration: %d maxlatency: %d nsamples: %d min: %g max: %g avg: %g (ns per timestamp unit)\n",
	       duration, maxlatency, nsamples, min, max, avg_cgt * 1000. / avg_ts);
}


/*
 * Mainprogram.
 */

void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "Usage: %s\n", progname);
	fprintf(stderr, "\t --duration\n");
	fprintf(stderr, "\t\tDuration of run in milliseconds (default 100).\n");
	fprintf(stderr, "\t --maxlatency\n");
	fprintf(stderr, "\t\tMaximum timestamp latency (default 5us).\n");
	fprintf(stderr, "\t --nsamples\n");
	fprintf(stderr, "\t\tNumber of samples (default 24).\n");
	exit(EXIT_FAILURE);
}

int main(int argc, char *argv[])
{
	int i = 1;

	while (i < argc) {
		if (strcmp(argv[i], "--duration") == 0) {
			duration = atoi(argv[++i]);
			if (duration <= 0)
				usage(argv[0], "%s: --duration argument must be positive.\n", argv[i]);
			++i;
		} else if (strcmp(argv[i], "--maxlatency") == 0) {
			maxlatency = atoi(argv[++i]);
			if (maxlatency <= 0)
				usage(argv[0], "%s: --maxlatency argument must be positive.\n", argv[i]);
			++i;
		} else if (strcmp(argv[i], "--nsamples") == 0) {
			nsamples = atoi(argv[++i]);
			if (nsamples <= 1)
				usage(argv[0], "%s: --nsamples argument must be positive.\n", argv[i]);
			++i;
		} else {
			usage(argv[0], "Unrecognized argument: %s\n", argv[i]);
		}
	}

	tscalibrate();

	return 0;
}
