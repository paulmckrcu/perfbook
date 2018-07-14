/*
 * lock.c: Demonstrate use of POSIX pthread_mutex_lock() and
 * 	pthread_mutex_unlock() primitives for parallel processing.
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

pthread_mutex_t lock_a = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock_b = PTHREAD_MUTEX_INITIALIZER;

int x = 0;

void *lock_reader(void *arg)
{
	int en;
	int i;
	int newx = -1;
	int oldx = -1;
	pthread_mutex_t *pmlp = (pthread_mutex_t *)arg;

	if ((en = pthread_mutex_lock(pmlp)) != 0) {
		fprintf(stderr, "lock_reader:pthread_mutex_lock: %s\n",
			strerror(en));
		exit(EXIT_FAILURE);
	}
	for (i = 0; i < 100; i++) {
		newx = READ_ONCE(x);
		if (newx != oldx) {
			printf("lock_reader(): x = %d\n", newx);
		}
		oldx = newx;
		poll(NULL, 0, 1);
	}
	if ((en = pthread_mutex_unlock(pmlp)) != 0) {
		fprintf(stderr, "lock_reader:pthread_mutex_lock: %s\n",
			strerror(en));
		exit(EXIT_FAILURE);
	}
	return NULL;
}

void *lock_writer(void *arg)
{
	int en;
	int i;
	pthread_mutex_t *pmlp = (pthread_mutex_t *)arg;

	if ((en = pthread_mutex_lock(pmlp)) != 0) {
		fprintf(stderr, "lock_writer:pthread_mutex_lock: %s\n",
			strerror(en));
		exit(EXIT_FAILURE);
	}
	for (i = 0; i < 3; i++) {
		WRITE_ONCE(x, READ_ONCE(x) + 1);
		poll(NULL, 0, 5);
	}
	if ((en = pthread_mutex_unlock(pmlp)) != 0) {
		fprintf(stderr, "lock_writer:pthread_mutex_lock: %s\n",
			strerror(en));
		exit(EXIT_FAILURE);
	}
	return NULL;
}

int main(int argc, char *argv[])
{
	int en; 
	pthread_t tid1;
	pthread_t tid2;
	void *vp;

	printf("Creating two threads using same lock:\n");
	if ((en = pthread_create(&tid1, NULL, lock_reader, &lock_a)) != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	if ((en = pthread_create(&tid2, NULL, lock_writer, &lock_a)) != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	if ((en = pthread_join(tid1, &vp)) != 0) {
		fprintf(stderr, "pthread_join: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	if ((en = pthread_join(tid2, &vp)) != 0) {
		fprintf(stderr, "pthread_join: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}

	printf("Creating two threads w/different locks:\n");
	x = 0;
	if ((en = pthread_create(&tid1, NULL, lock_reader, &lock_a)) != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	if ((en = pthread_create(&tid2, NULL, lock_writer, &lock_b)) != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	if ((en = pthread_join(tid1, &vp)) != 0) {
		fprintf(stderr, "pthread_join: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	if ((en = pthread_join(tid2, &vp)) != 0) {
		fprintf(stderr, "pthread_join: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}

	return EXIT_SUCCESS;
}
