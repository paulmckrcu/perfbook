/*
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
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

#include "../util.h"

long maxdelta = 1000;
#define NWATCHERS 4

pthread_mutex_t snaplock = PTHREAD_MUTEX_INITIALIZER;

static int modgreater(long a, long b)
{
	return ((a - b) > 0);
}

struct snapshot {
	double t;
	long a;
	long b;
	long c;
} ss = {0.0, 0, 0, 0};

int goflag = 0;

int producer_ready = 0;
int producer_done = 0;

void *producer(void *ignored)
{
	int i = 0;

	producer_ready = 1;
	while (!goflag)
		sched_yield();
	while (goflag) {
		if (pthread_mutex_lock(&snaplock) != 0) {
			perror("producer pthread_mutex_lock");
			exit(-1);
		}
		ss.t = dgettimeofday();
		ss.a = ss.c + 1;
		ss.b = ss.a + 1;
		ss.c = ss.b + 1;
		if (pthread_mutex_unlock(&snaplock) != 0) {
			perror("producer pthread_mutex_unlock");
			exit(-1);
		}
		i++;
	}
	printf("producer exiting: %d samples\n", i);
	producer_done = 1;
	return (NULL);
}

#define NSNAPS	100

struct snapshot_consumer {
	double t;
	double tc;
	long a;
	long b;
	long c;
	long sequence;
	int iserror;
} ssc[NSNAPS];

int curseq = 0;

int consumer_ready = 0;
int consumer_done = 0;

void *consumer(void *ignored)
{
	struct snapshot_consumer curssc;
	int i = 0;
	int j = 0;

	consumer_ready = 1;
	while (ss.t == 0.0) {
		sched_yield();
	}
	while (goflag) {
		if (pthread_mutex_lock(&snaplock) != 0) {
			perror("consumer pthread_mutex_lock");
			exit(-1);
		}
		curssc.tc = dgettimeofday();
		curssc.t = ss.t;
		curssc.a = ss.a;
		curssc.b = ss.b;
		curssc.c = ss.c;
		if (pthread_mutex_unlock(&snaplock) != 0) {
			perror("consumer pthread_mutex_unlock");
			exit(-1);
		}
		curssc.sequence = curseq;
		curssc.iserror = 0;
		if ((curssc.t > curssc.tc) ||
		    modgreater(ssc[i].a, curssc.a) ||
		    modgreater(ssc[i].b, curssc.b) ||
		    modgreater(ssc[i].c, curssc.c) ||
		    modgreater(curssc.a, ssc[i].a + maxdelta) ||
		    modgreater(curssc.b, ssc[i].b + maxdelta) ||
		    modgreater(curssc.c, ssc[i].c + maxdelta)) {
			i++;
			curssc.iserror = 1;
		} else if (ssc[i].iserror)
			i++;
		ssc[i] = curssc;
		curseq++;
		if (i + 1 >= NSNAPS)
			break;
	}
	printf("consumer exited loop, collected %d items out of %d\n",
	       i, curseq);
	if (ssc[0].iserror)
		printf("0/%d: %.6f %.6f (%.3f) %d %d %d\n",
		       ssc[0].sequence, 
		       ssc[j].t, ssc[j].tc, (ssc[j].tc - ssc[j].t) * 1000000,
		       ssc[j].a, ssc[j].b, ssc[j].c);
	for (j = 0; j <= i; j++)
		if (ssc[j].iserror)
			printf("%d/%d: %.6f (%.3f) %d %d %d\n",
			       j, ssc[j].sequence,
			       ssc[j].t, (ssc[j].tc - ssc[j].t) * 1000000,
			       ssc[j].a - ssc[j - 1].a,
			       ssc[j].b - ssc[j - 1].b,
			       ssc[j].c - ssc[j - 1].c);
	consumer_done = 1;
}

int watcher_ready = 0;

void *watcher(void *ignored)
{
	int sum = 0;

	watcher_ready++;
	while (!goflag)
		sum += ss.a + ss.b + ss.c;
	return (void*)sum;
}

int main(int argc, char *argv[])
{
	int i;
	pthread_t id;
	double starttime;

	if (pthread_create(&id, NULL, producer, NULL) != 0) {
		perror("pthread_create producer");
		exit(-1);
	}
	if (pthread_create(&id, NULL, consumer, NULL) != 0) {
		perror("pthread_create consumer");
		exit(-1);
	}
	for (i = 0; i < NWATCHERS; i++)
		if (pthread_create(&id, NULL, watcher, (void *)i) != 0) {
			perror("pthread_create watcher");
			exit(-1);
		}
	while (!producer_ready || !consumer_ready)
		sched_yield();
	goflag = 1;
	starttime = dgettimeofday();
	while ((dgettimeofday() - starttime < 3) && !consumer_done)
		poll(NULL, 0, 1);
	goflag = 0;
	while (!consumer_done || !producer_done)
		poll(NULL, 0, 1);
	exit(0);
}
