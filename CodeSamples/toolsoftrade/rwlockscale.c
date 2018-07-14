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
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <errno.h>
#include "../api.h"

pthread_rwlock_t rwl = PTHREAD_RWLOCK_INITIALIZER;
int holdtime = 0;	/* # loops holding lock. */
int thinktime = 0;	/* # loops not holding lock. */
long long *readcounts;
int nreadersrunning = 0;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2
char goflag = GOFLAG_INIT;

void *reader(void *arg)
{
	int en;
	int i;
	long long loopcnt = 0;
	long me = (long)arg;

	__sync_fetch_and_add(&nreadersrunning, 1);
	while (READ_ONCE(goflag) == GOFLAG_INIT) {
		continue;
	}
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		if ((en = pthread_rwlock_rdlock(&rwl)) != 0) {
			perror("pthread_rwlock_rdlock");
			exit(EXIT_FAILURE);
		}
		for (i = 1; i < holdtime; i++) {
			barrier();
		}
		if ((en = pthread_rwlock_unlock(&rwl)) != 0) {
			perror("pthread_rwlock_unlock");
			exit(EXIT_FAILURE);
		}
		for (i = 1; i < thinktime; i++) {
			barrier();
		}
		loopcnt++;
	}
	readcounts[me] = loopcnt;
	return NULL;
}

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
			perror("pthread_create");
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
			perror("pthread_join");
			exit(EXIT_FAILURE);
		}
	}
	for (i = 0; i < nthreads; i++) {
		sum += readcounts[i];
	}

	printf("%s n: %d  h: %d t: %d  sum: %lld\n",
	       argv[0], nthreads, holdtime, thinktime, sum);

	return EXIT_SUCCESS;
}
