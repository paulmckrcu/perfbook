/*
 * temporal.c: Demonstrate temporal properties and not of coe, fre, and rfe
 *
 * This test produces output as follows:
 *
 * ./temporal --coe --nthreads 10
 * ./temporal arguments: coe nthread 10 duration: 100
 * 0 2254916 0 2255000
 * 0 2255612 6 2255828
 * 0 2256452 4 2256520
 * 0 242507054 4 242507152
 * 1 2254816 3 2254904
 * 1 2256568 4 2256788
 * 1 242507190 4 242507260
 * 2 2254696 3 2254780
 * 2 2257168 4 2257328
 * 2 242507064 4 242507154
 * 3 2254604 3 2254680
 * 3 2255884 4 2255956
 * 3 242506966 4 242507096
 * 4 2254732 4 2254816
 * 4 242506984 4 242507072
 * 5 2254388 4 2254612
 * 5 242507040 4 242507140
 * 6 2255156 6 2255232
 * 6 2256376 4 2256740
 * 6 242506970 4 242507192
 * 7 2254832 3 2255288
 * 7 2256464 4 2256532
 * 7 242507038 4 242507126
 * 8 2254800 3 2254888
 * 8 2256444 4 2256916
 * 8 242507086 4 242507108
 * 9 2254676 3 2254764
 * 9 2257188 4 2257456
 * 9 242506834 4 242507130
 *
 * The columns are thread number, start time in nanoseconds, value of
 * shared variable, and end time in nanoseconds.
 *
 * The --fre and --rfe arguments also produce a line as follows:
 *
 * Write 122438044 1 122438062
 *
 * This records the times and values of the write that the other threads
 * are reading from.
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

/*
 * Test variables.
 */

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

static int coe;
static int duration = 100;
static int fre;
static int nthreads = 1;
static int rfe;

static int sharedvar __attribute__((__aligned__(CACHE_LINE_SIZE)));

struct sample {
	int value;
	long long tbefore;
	long long tafter;
};

struct sample_data {
	int sd_me; // My integer ID.
	int sd_started; // This thread has begun executing.
	void (*sd_func)(struct sample_data *); // Init function, if non-NULL.
	int sd_n; // Number of entries in ->sd_samples array.
	int sd_nsamples; // Number of samples collected.
	struct sample *sd_samples; // Array for sample collection.
};

// Read clock, sharedvar, clock and store in the specified struct sample.
void readval(struct sample *sp)
{
	sp->tbefore = get_timestamp();
	sp->value = READ_ONCE(sharedvar);
	sp->tafter = get_timestamp();
}

// Collect unique data reads, timestamped.  If there are multiple reads
// of the same value, the beginning timestamp for the first read are and
// the ending timestamp for the last read are retained.
void collect_data(struct sample_data *sdp)
{
	int i = 1;
	struct sample s;
	struct sample *sp;

	readval(&sdp->sd_samples[0]);
	sdp->sd_nsamples = 1;
	sp = &sdp->sd_samples[1];
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		readval(&s);
		if (s.value == sp[-1].value) {
			sp[-1].tafter = s.tafter;
			sp[0] = s;
		} else {
			if (fre) {
				sdp->sd_nsamples = i + 1;
				if (++i >= sdp->sd_n)
					break;
				sp++;
				sp[0] = s;
			}
			sdp->sd_nsamples = i + 1;
			if (++i >= sdp->sd_n)
				break;
			sp++;
			sp[0] = s;
		}
	}
}

// Generic child thread, with ->sd_func to invoke.  Or not.
void *child_thread(void *args)
{
	struct sample_data *sdp = args;

	WRITE_ONCE(sdp->sd_started, 1);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		continue;
	if (sdp->sd_func)
		sdp->sd_func(sdp);
	collect_data(sdp);
	return NULL;
}

// Create all child threads and wait for them to start executing.
// cf() is the child's initialization function or NULL, and n is
// the maximum number of samples.
struct sample_data *create_all_threads(void (*cf)(struct sample_data *), int n)
{
	int i;
	struct sample_data *sdp = calloc(nthreads, sizeof(sdp[0]));

	// Allocate memory and start child threads.
	BUG_ON(!sdp);
	for (i = 0; i < nthreads; i++) {
		sdp[i].sd_me = i;
		sdp[i].sd_n = n;
		sdp[i].sd_started = 0;
		sdp[i].sd_func = cf;
		sdp[i].sd_nsamples = 0;
		sdp[i].sd_samples = calloc(n, sizeof(sdp[i].sd_samples[0]));
		BUG_ON(!sdp[i].sd_samples);
		create_thread(child_thread, (void *)&sdp[i]);
	}

	// Wait for all child threads to start actually executing.
	for (i = 0; i < nthreads; i++)
		while (!READ_ONCE(sdp[i].sd_started))
			continue;

	return sdp;
}

// Dump data from all child threads.  If the parent thread needs something
// dumped, it must dump it itself.
void dump_all_threads(struct sample_data *sdp, long long *tsp)
{
	int cnum;
	int i;
	long long mintime;
	struct sample *sp;
	long long tsdelta1;
	long long tsdelta2;

	for (cnum = 0; cnum < nthreads; cnum++) {
		for (i = 0; i < sdp[cnum].sd_nsamples; i++) {
			sp = &sdp[cnum].sd_samples[i];
			tsdelta1 = sp->tbefore - *tsp;
			tsdelta2 = sp->tafter - *tsp;
			printf("%d %lld %d %lld\n", cnum,
			       tsdelta1, sp->value, tsdelta2);
		}
	}
}

// The coe child threads write their ID after starting up.
void coe_start(struct sample_data *sdp)
{
	WRITE_ONCE(sharedvar, sdp->sd_me);
}

// The coe parent lets the children do the writing.
void coe_parent(void)
{
	struct sample_data *sdp;
	long long ts;

	sharedvar = -1;
	ts = get_timestamp();
	sdp = create_all_threads(coe_start, 2 * nthreads);
	WRITE_ONCE(goflag, GOFLAG_RUN);
	poll(NULL, 0, duration);
	WRITE_ONCE(goflag, GOFLAG_STOP);
	wait_all_threads();
	dump_all_threads(sdp, &ts);
}

// The fre and rfe parent threads do the writing themselves.
void fre_rfe_parent(void)
{
	struct sample_data *sdp;
	long long ts;
	long long tsafter;
	long long tsbefore;

	sharedvar = 0;
	ts = get_timestamp();
	sdp = create_all_threads(NULL, 3);
	WRITE_ONCE(goflag, GOFLAG_RUN);
	poll(NULL, 0, (duration + 1) / 2);
	tsbefore = get_timestamp();
	WRITE_ONCE(sharedvar, 1);
	tsafter = get_timestamp();
	poll(NULL, 0, (duration + 1) / 2);
	WRITE_ONCE(goflag, GOFLAG_STOP);
	wait_all_threads();
	dump_all_threads(sdp, &ts);
	tsbefore = tsbefore - ts;
	tsafter = tsafter - ts;
	printf("Write %lld 1 %lld\n", tsbefore, tsafter);
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
	fprintf(stderr, "\t --coe\n");
	fprintf(stderr, "\t\tCollect coherence (modification order) times.\n");
	fprintf(stderr, "\t --fre\n");
	fprintf(stderr, "\t\tCollect from-read time.\n");
	fprintf(stderr, "\t --rfe\n");
	fprintf(stderr, "\t\tCollect read-from time.\n");
	fprintf(stderr, "\t --nthreads\n");
	fprintf(stderr, "\t\tNumber of measurement threads (#CPUs-1).\n");
	fprintf(stderr, "\t --duration\n");
	fprintf(stderr, "\t\tDuration of run in milliseconds (default 100).\n");
	exit(EXIT_FAILURE);
}

int main(int argc, char *argv[])
{
	int i = 1;

	smp_init();

	while (i < argc) {
		if (strcmp(argv[i], "--coe") == 0) {
			if (coe + fre + rfe != 0)
				usage(argv[0], "%s: Only one of --coe, --fre, and rfe may be specified.\n", argv[i = 1]);
			coe = 1;
			++i;
		} else if (strcmp(argv[i], "--fre") == 0) {
			if (coe + fre + rfe != 0)
				usage(argv[0], "%s: Only one of --coe, --fre, and rfe may be specified.\n", argv[i = 1]);
			fre = 1;
			++i;
		} else if (strcmp(argv[i], "--rfe") == 0) {
			if (coe + fre + rfe != 0)
				usage(argv[0], "%s: Only one of --coe, --fre, and rfe may be specified.\n", argv[i = 1]);
			rfe = 1;
			++i;
		} else if (strcmp(argv[i], "--nthreads") == 0) {
			nthreads = atoi(argv[++i]);
			if (nthreads <= 0)
				usage(argv[0], "%d: --nthreads argument must be positive.\n", argv[i = 1]);
			++i;
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = atoi(argv[++i]);
			if (duration <= 0)
				usage(argv[0], "%d: --duration argument must be positive.\n", argv[i = 1]);
			++i;
		} else {
			usage(argv[0], "Unrecognized argument: %s\n", argv[i]);
		}
	}
	if (coe + fre + rfe == 0)
		usage(argv[0], "%s: At least one of --coe, --fre, and rfe must be specified.\n", argv[i = 1]);

	// Dump arguments.
	printf("%s arguments: %s nthread %d duration: %d\n",
	       argv[0], coe ? "coe" : fre ? "fre" : "rfe", nthreads, duration);

	if (coe)
		coe_parent();
	else
		fre_rfe_parent();

	return 0;
}
