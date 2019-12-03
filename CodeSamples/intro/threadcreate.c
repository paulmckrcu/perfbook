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
 * Copyright (c) 2006-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

//\begin{snippet}[labelbase=ln:intro:threadcreate:thread_test,commandchars=\@\[\]]
void *thread_test(void *arg)
{
	int myarg = (intptr_t)arg;

	printf("child thread %d: smp_thread_id() = %d\n",
	       myarg, smp_thread_id());
	return NULL;				//\lnlbl{return}
}
//\end{snippet}

void usage(char *progname)
{
	fprintf(stderr,
		"Usage: %s [ #threads ]\n", progname);
	exit(-1);
}

//\begin{snippet}[labelbase=ln:intro:threadcreate:main,commandchars=\@\^\$]
int main(int argc, char *argv[])
{
	int i;
	int nkids = 1;

	smp_init();					//\lnlbl{smp_init}

	if (argc > 1) {					//\lnlbl{parse:b}
		nkids = strtoul(argv[1], NULL, 0);
		if (nkids > NR_THREADS) {
			fprintf(stderr, "nkids = %d too large, max = %d\n",
				nkids, NR_THREADS);
			usage(argv[0]);
		}
	}						//\lnlbl{parse:e}
	printf("Parent thread spawning %d threads.\n", nkids); //\lnlbl{announce}

	for (i = 0; i < nkids; i++)			//\lnlbl{create:b}
		create_thread(thread_test, (void *)(intptr_t)i); //\lnlbl{create:e}

	wait_all_threads();				//\lnlbl{wait}

	printf("All spawned threads completed.\n");

	exit(0);
}
//\end{snippet}
