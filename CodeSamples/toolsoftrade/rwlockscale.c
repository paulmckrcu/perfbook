/*
 * rwlockscale.c: Demonstrate scalability of POSIX pthread_rwlock_rdlock()
 *	and pthread_rwlock_unlock().
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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <errno.h>
#include "../api.h"
#include "../api-pthreads/util.h"

//\begin{snippet}[labelbase=ln:toolsoftrade:rwlockscale:reader,commandchars=\@\^\$]
pthread_rwlock_t rwl = PTHREAD_RWLOCK_INITIALIZER;	//\lnlbl{rwlock}
unsigned long holdtime = 0;	/* # loops w/lock. */	//\lnlbl{holdtm}
unsigned long thinktime = 0;	/* # w/out lock. */	//\lnlbl{thinktm}
long long *readcounts;					//\lnlbl{rdcnts}
int nreadersrunning = 0;				//\lnlbl{nrdrun}

#define GOFLAG_INIT 0					//\lnlbl{goflag:b}
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2
char goflag = GOFLAG_INIT;				//\lnlbl{goflag:e}

void *reader(void *arg)					//\lnlbl{reader:b}
{
	int en;
	int i;
	long long loopcnt = 0;
	long me = (long)arg;

	__sync_fetch_and_add(&nreadersrunning, 1);	//\lnlbl{reader:atmc_inc}
	while (READ_ONCE(goflag) == GOFLAG_INIT) {	//\lnlbl{reader:wait:b}
		continue;
	}						//\lnlbl{reader:wait:e}
	while (READ_ONCE(goflag) == GOFLAG_RUN) {	//\lnlbl{reader:loop:b}
		if ((en = pthread_rwlock_rdlock(&rwl)) != 0) {	//\lnlbl{reader:acq:b}
			fprintf(stderr,
			        "pthread_rwlock_rdlock: %s\n", strerror(en));
			exit(EXIT_FAILURE);
		}						//\lnlbl{reader:acq:e}
		for (i = 1; i < holdtime; i++) {	//\lnlbl{reader:hold:b}
			wait_microseconds(1);
		}					//\lnlbl{reader:hold:e}
		if ((en = pthread_rwlock_unlock(&rwl)) != 0) {	//\lnlbl{reader:rel:b}
			fprintf(stderr,
				"pthread_rwlock_unlock: %s\n", strerror(en));
			exit(EXIT_FAILURE);
		}						//\lnlbl{reader:rel:e}
		for (i = 1; i < thinktime; i++) {	//\lnlbl{reader:think:b}
			wait_microseconds(1);
		}					//\lnlbl{reader:think:e}
		loopcnt++;				//\lnlbl{reader:count}
	}						//\lnlbl{reader:loop:e}
	readcounts[me] = loopcnt;			//\lnlbl{reader:mov_cnt}
	return NULL;					//\lnlbl{reader:return}
}							//\lnlbl{reader:e}
//\end{snippet}

int main(int argc, char *argv[])
{
	int en;
	long i;
	int nthreads;
	long long sum = 0LL;
	pthread_t *tid;
	void *vp;

	if (argc != 4) {
		fprintf(stderr,
			"Usage: %s nthreads holdloops thinkloops\n", argv[0]);
		exit(EXIT_FAILURE);
	}
	nthreads = strtoul(argv[1], NULL, 0);
	holdtime = strtoul(argv[2], NULL, 0);
	thinktime = strtoul(argv[3], NULL, 0);
	readcounts = malloc(nthreads * sizeof(readcounts[0]));
	tid = malloc(nthreads * sizeof(tid[0]));
	if (readcounts == NULL || tid == NULL) {
		fprintf(stderr, "Out of memory\n");
		exit(EXIT_FAILURE);
	}
	for (i = 0; i < nthreads; i++) {
		en = pthread_create(&tid[i], NULL, reader, (void *)i);
		if (en != 0) {
			fprintf(stderr, "pthread_create: %s\n", strerror(en));
			exit(EXIT_FAILURE);
		}
	}
	while (READ_ONCE(nreadersrunning) < nthreads) {
		continue;
	}
	goflag = GOFLAG_RUN;
	sleep(1);
	goflag = GOFLAG_STOP;

	for (i = 0; i < nthreads; i++) {
		if ((en = pthread_join(tid[i], &vp)) != 0) {
			fprintf(stderr, "pthread_join: %s\n", strerror(en));
			exit(EXIT_FAILURE);
		}
	}
	for (i = 0; i < nthreads; i++) {
		sum += readcounts[i];
	}

	printf("%s n: %d  h: %lu t: %lu  sum: %lld\n",
	       argv[0], nthreads, holdtime, thinktime, sum);

	return EXIT_SUCCESS;
}
