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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <errno.h>
#include "../api.h"

//\begin{snippet}[labelbase=ln:toolsoftrade:lock:reader_writer,commandchars=\$\[\]]
pthread_mutex_t lock_a = PTHREAD_MUTEX_INITIALIZER;	//\lnlbl{lock_a}
pthread_mutex_t lock_b = PTHREAD_MUTEX_INITIALIZER;	//\lnlbl{lock_b}

int x = 0;						//\lnlbl{x}

void *lock_reader(void *arg)				//\lnlbl{reader:b}
{
	int en;
	int i;
	int newx = -1;
	int oldx = -1;
	pthread_mutex_t *pmlp = (pthread_mutex_t *)arg;	//\lnlbl{reader:cast}

	if ((en = pthread_mutex_lock(pmlp)) != 0) {	//\lnlbl{reader:acq:b}
		fprintf(stderr, "lock_reader:pthread_mutex_lock: %s\n",
			strerror(en));
		exit(EXIT_FAILURE);
	}						//\lnlbl{reader:acq:e}
	for (i = 0; i < 100; i++) {			//\lnlbl{reader:loop:b}
		newx = READ_ONCE(x);			//\lnlbl{reader:read_x}
		if (newx != oldx) {
			printf("lock_reader(): x = %d\n", newx);
		}
		oldx = newx;
		poll(NULL, 0, 1);			//\lnlbl{reader:sleep}
	}						//\lnlbl{reader:loop:e}
	if ((en = pthread_mutex_unlock(pmlp)) != 0) {	//\lnlbl{reader:rel:b}
		fprintf(stderr, "lock_reader:pthread_mutex_unlock: %s\n",
			strerror(en));
		exit(EXIT_FAILURE);
	}						//\lnlbl{reader:rel:e}
	return NULL;					//\lnlbl{reader:return}
}							//\lnlbl{reader:e}

void *lock_writer(void *arg)				//\lnlbl{writer:b}
{
	int en;
	int i;
	pthread_mutex_t *pmlp = (pthread_mutex_t *)arg;	//\lnlbl{writer:cast}

	if ((en = pthread_mutex_lock(pmlp)) != 0) {	//\lnlbl{writer:acq:b}
		fprintf(stderr, "lock_writer:pthread_mutex_lock: %s\n",
			strerror(en));
		exit(EXIT_FAILURE);
	}						//\lnlbl{writer:acq:e}
	for (i = 0; i < 3; i++) {			//\lnlbl{writer:loop:b}
		WRITE_ONCE(x, READ_ONCE(x) + 1);	//\lnlbl{writer:inc}
		poll(NULL, 0, 5);
	}						//\lnlbl{writer:loop:e}
	if ((en = pthread_mutex_unlock(pmlp)) != 0) {	//\lnlbl{writer:rel:b}
		fprintf(stderr, "lock_writer:pthread_mutex_unlock: %s\n",
			strerror(en));
		exit(EXIT_FAILURE);
	}						//\lnlbl{writer:rel:e}
	return NULL;
}							//\lnlbl{writer:e}
//\end{snippet}

int main(int argc, char *argv[])
{
	int en; 
	pthread_t tid1;
	pthread_t tid2;
	void *vp;

//\begin{snippet}[labelbase=ln:toolsoftrade:lock:same_lock,commandchars=\$\[\]]
	printf("Creating two threads using same lock:\n");
	en = pthread_create(&tid1, NULL, lock_reader, &lock_a);	//\lnlbl{cr:reader:b}
	if (en != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}							//\lnlbl{cr:reader:e}
	en = pthread_create(&tid2, NULL, lock_writer, &lock_a); //\lnlbl{cr:writer:b}
	if (en != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}							//\lnlbl{cr:writer:e}
	if ((en = pthread_join(tid1, &vp)) != 0) {	//\lnlbl{wait:b}
		fprintf(stderr, "pthread_join: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	if ((en = pthread_join(tid2, &vp)) != 0) {
		fprintf(stderr, "pthread_join: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}						//\lnlbl{wait:e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:toolsoftrade:lock:diff_lock,commandchars=\$\[\]]
	printf("Creating two threads w/different locks:\n");
	x = 0;
	en = pthread_create(&tid1, NULL, lock_reader, &lock_a);
	if (en != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	en = pthread_create(&tid2, NULL, lock_writer, &lock_b);
	if (en != 0) {
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
//\end{snippet}

	return EXIT_SUCCESS;
}
