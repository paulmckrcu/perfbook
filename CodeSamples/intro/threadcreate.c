/*
 * threadcreate.c: simple program demonstrating thread primitives.
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
 * Copyright (c) 2006 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"

void *thread_test(void *arg)
{
	int myarg = (intptr_t)arg;

	printf("child thread %d: smp_thread_id() = %d\n",
	       myarg, smp_thread_id());
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
	printf("Parent thread spawning %d threads.\n", nkids);

	for (i = 0; i < nkids; i++)
		create_thread(thread_test, (void *)(intptr_t)i);

	wait_all_threads();

	printf("All spawned threads completed.\n");

	exit(0);
}
