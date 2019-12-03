/*
 * initraceperf.c: simple program comparing lock and flag check.
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

#include "../api.h"

spinlock_t mutex;
long long counter;
int goflag;
int initialized = 0;

void initcounter(void)
{
	spin_lock_init(&mutex);
}

void *counter_test(void *arg)
{
	long long mycounter = 0LL;

	while (goflag < 0)
		continue;
	while (goflag) {
		if (!initialized) {
			spin_lock(&mutex);
			initialized = 1;
			spin_unlock(&mutex);
		}
		mycounter++;
	}
	spin_lock(&mutex);
	counter += mycounter;
	spin_unlock(&mutex);
	return NULL;
}

void usage(char *progname)
{
	fprintf(stderr,
		"Usage: %s [ #threads ]\n", progname);
	exit(-1);
}

int main(int argc, char *argv[])
{
	int i;
	int nkids = 1;

	smp_init();

	if (argc > 1) {
		nkids = strtoul(argv[1], NULL, 0);
		if (nkids > NR_THREADS) {
			fprintf(stderr, "nkids = %d too large, max = %d\n",
				nkids, NR_THREADS);
			usage(argv[0]);
		}
	}
	printf("%d ", nkids);

	goflag = -1;
	counter = 0LL;
	for (i = 0; i < nkids; i++)
		create_thread(counter_test, NULL);

	goflag = 1;
	sleep(1);
	goflag = 0;

	wait_all_threads();

	printf("count: %lld\n", counter);

	exit(0);
}
