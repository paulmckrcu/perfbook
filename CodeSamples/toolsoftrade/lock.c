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
	int i;
	int newx = -1;
	int oldx = -1;
	pthread_mutex_t *pmlp = (pthread_mutex_t *)arg;

	if (pthread_mutex_lock(pmlp) != 0) {
		perror("lock_reader:pthread_mutex_lock");
		exit(-1);
	}
	for (i = 0; i < 100; i++) {
		newx = READ_ONCE(x);
		if (newx != oldx) {
			printf("lock_reader(): x = %d\n", newx);
		}
		oldx = newx;
		poll(NULL, 0, 1);
	}
	if (pthread_mutex_unlock(pmlp) != 0) {
		perror("lock_reader:pthread_mutex_unlock");
		exit(-1);
	}
	return NULL;
}

void *lock_writer(void *arg)
{
	int i;
	pthread_mutex_t *pmlp = (pthread_mutex_t *)arg;

	if (pthread_mutex_lock(pmlp) != 0) {
		perror("lock_writer:pthread_mutex_lock");
		exit(-1);
	}
	for (i = 0; i < 3; i++) {
		WRITE_ONCE(x, READ_ONCE(x) + 1);
		poll(NULL, 0, 5);
	}
	if (pthread_mutex_unlock(pmlp) != 0) {
		perror("lock_writer:pthread_mutex_unlock");
		exit(-1);
	}
	return NULL;
}

int main(int argc, char *argv[])
{
	pthread_t tid1;
	pthread_t tid2;
	void *vp;

	printf("Creating two threads using same lock:\n");
	if (pthread_create(&tid1, NULL, lock_reader, &lock_a) != 0) {
		perror("pthread_create");
		exit(-1);
	}
	if (pthread_create(&tid2, NULL, lock_writer, &lock_a) != 0) {
		perror("pthread_create");
		exit(-1);
	}
	if (pthread_join(tid1, &vp) != 0) {
		perror("pthread_join");
		exit(-1);
	}
	if (pthread_join(tid2, &vp) != 0) {
		perror("pthread_join");
		exit(-1);
	}

	printf("Creating two threads w/different locks:\n");
	x = 0;
	if (pthread_create(&tid1, NULL, lock_reader, &lock_a) != 0) {
		perror("pthread_create");
		exit(-1);
	}
	if (pthread_create(&tid2, NULL, lock_writer, &lock_b) != 0) {
		perror("pthread_create");
		exit(-1);
	}
	if (pthread_join(tid1, &vp) != 0) {
		perror("pthread_join");
		exit(-1);
	}
	if (pthread_join(tid2, &vp) != 0) {
		perror("pthread_join");
		exit(-1);
	}

	return 0;
}
