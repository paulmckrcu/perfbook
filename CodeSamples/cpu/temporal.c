/*
 * temporal.c: Demonstrate temporal properties and not of coe, fre, and rfe
 *
 * This test produces output as follows:
 *
 * ./temporal --coe --nthreads 4
 * ./temporal arguments: coe nthread 4 duration: 100
 * COE-write 0 1178028 0 1178116 1178028 1178116
 * 0 1178188 0 1178384 1178188 1178384
 * COE-write 1 1177608 1 1177692 1177608 1177692
 * 1 1177976 1 1178064 1178144 1178216
 * COE-write 2 1178088 2 1178164 1178088 1178164
 * 2 1178532 2 1178880 1178532 1178880
 * COE-write 3 1177964 3 1178044 1177964 1178044
 * 3 1178320 3 1178408 241441564 241441580
 * COE-final 3
 *
 * The columns are thread number, start time of the first sample, value
 * of shared variable, end time of the first sample, the start time of
 * the last sample, and the end time of the last sample.  All times are
 * in nanoseconds since (roughly) the beginning of the run.  If a given
 * value was observed by only one read, the times for the first and last
 * samples will be identical.
 *
 * The --coe argument also produces lines as follows:
 *
 * COE-write 0 333512 0 333584 333512 333584
 *
 * The format is the same as for the fully numeric lines shown above,
 * except that the third numeric column is the value written instead
 * of the thread ID, though these two numbers should be identical.
 * Thess lines time the actual write from the corresponding thread.
 *
 * The COE-final line identifies the winning write, that is, the
 * write whose value persisted to the end of the test.
 *
 * The --fre and --rfe arguments also produce a line as follows:
 *
 * Write 121297118 1 121297136 121297118 121297136
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
	long long tbeforelast;
	long long tafter;
	long long tafterlast;
};

struct sample_data {
	int sd_me; // My integer ID.
	int sd_started; // This thread has begun executing.
	void (*sd_func)(struct sample_data *); // Init function, if non-NULL.
	int sd_n; // Number of entries in ->sd_samples array.
	struct sample coe_sample; // Start and time for initial coe write.
	int sd_nsamples; // Number of samples collected.
	struct sample *sd_samples; // Array for sample collection.
};

// Read clock, sharedvar, clock and store in the specified struct sample.
void readval(struct sample *sp)
{
	sp->tbefore = get_timestamp();
	sp->tbeforelast = sp->tbefore;
	sp->value = READ_ONCE(sharedvar);
	sp->tafter = get_timestamp();
	sp->tafterlast = sp->tafter;
}

// Collect unique data reads, timestamped.  If there are multiple reads
// of the same value, the beginning timestamp for the first read are and
// the ending timestamp for the last read are retained.
void collect_data(struct sample_data *sdp)
{
	int i = 1;
	int n = sdp->sd_n;
	struct sample s;
	struct sample *sp;

	sp = &sdp->sd_samples[0];
	readval(sp);
	sdp->sd_nsamples = 1;
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		readval(&s);
		if (s.value == sp->value) {
			sp->tbeforelast = s.tbefore;
			sp->tafterlast = s.tafter;
		} else {
			if (++i >= n)
				break;
			sp++;
			*sp = s;
		}
	}
	sdp->sd_nsamples = i;
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
	struct sample *sp;
	long long tsdelta1;
	long long tsdelta2;
	long long tsdelta3;
	long long tsdelta4;

	for (cnum = 0; cnum < nthreads; cnum++) {
		if (coe) {
			int me = sdp[cnum].sd_me;
			struct sample *sp = &sdp[cnum].coe_sample;

			tsdelta1 = sp->tbefore - *tsp;
			tsdelta2 = sp->tafter - *tsp;
			tsdelta3 = sp->tbeforelast - *tsp;
			tsdelta4 = sp->tafterlast - *tsp;
			printf("COE-write %d %lld %d %lld %lld %lld\n", cnum,
			       tsdelta1, me, tsdelta2, tsdelta3, tsdelta4);
		}
		for (i = 0; i < sdp[cnum].sd_nsamples; i++) {
			sp = &sdp[cnum].sd_samples[i];
			tsdelta1 = sp->tbefore - *tsp;
			tsdelta2 = sp->tafter - *tsp;
			tsdelta3 = sp->tbeforelast - *tsp;
			tsdelta4 = sp->tafterlast - *tsp;
			printf("%d %lld %d %lld %lld %lld\n", cnum,
			       tsdelta1, sp->value, tsdelta2, tsdelta3, tsdelta4);
		}
	}
}

// The coe child threads write their ID after starting up.
void coe_start(struct sample_data *sdp)
{
	struct sample *sp = &sdp->coe_sample;

	sp->value = -1;
	sp->tbefore = get_timestamp();
	sp->tbeforelast = sp->tbefore;
	WRITE_ONCE(sharedvar, sdp->sd_me);
	sp->tafter = get_timestamp();
	sp->tafterlast = sp->tafter;
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
	printf("COE-final %d\n", sharedvar);
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
	sdp = create_all_threads(NULL, 5);
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
	printf("Write %lld 1 %lld %lld %lld\n",
	       tsbefore, tsafter, tsbefore, tsafter);
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
				usage(argv[0], "Only one of --coe, --fre, and rfe may be specified.\n");
			coe = 1;
			++i;
		} else if (strcmp(argv[i], "--fre") == 0) {
			if (coe + fre + rfe != 0)
				usage(argv[0], "Only one of --coe, --fre, and rfe may be specified.\n");
			fre = 1;
			++i;
		} else if (strcmp(argv[i], "--rfe") == 0) {
			if (coe + fre + rfe != 0)
				usage(argv[0], "Only one of --coe, --fre, and rfe may be specified.\n");
			rfe = 1;
			++i;
		} else if (strcmp(argv[i], "--nthreads") == 0) {
			nthreads = atoi(argv[++i]);
			if (nthreads <= 0)
				usage(argv[0], "%s: --nthreads argument must be positive integer.\n", argv[i]);
			++i;
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = atoi(argv[++i]);
			if (duration <= 0)
				usage(argv[0], "%s: --duration argument must be positive integer.\n", argv[i]);
			++i;
		} else {
			usage(argv[0], "Unrecognized argument: %s\n");
		}
	}
	if (coe + fre + rfe == 0)
		usage(argv[0], "At least one of --coe, --fre, and rfe must be specified.\n");

	// Dump arguments.
	printf("%s arguments: %s nthread %d duration: %d\n",
	       argv[0], coe ? "coe" : fre ? "fre" : "rfe", nthreads, duration);

	if (coe)
		coe_parent();
	else
		fre_rfe_parent();

	return 0;
}
