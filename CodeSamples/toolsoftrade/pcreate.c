/*
 * pcreate.c: Demonstrate use of POSIX pthread_create() and pthread_join()
 *	primitives for parallel processing.
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

// \begin{snippet}[labelbase=ln:toolsoftrade:pcreate:mythread,keepcomment=yes,commandchars=\$\@\^]
int x = 0;

void *mythread(void *arg)
{
	x = 1;
	printf("Child process set x=1\n");
	return NULL;
}

int main(int argc, char *argv[])
{
	int en;
	pthread_t tid;
	void *vp;

	if ((en = pthread_create(&tid, NULL,		//\lnlbl{create:a}
	                         mythread, NULL)) != 0) {//\lnlbl{create:b}
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}

	/* parent */

	if ((en = pthread_join(tid, &vp)) != 0) {	//\lnlbl{join}
		fprintf(stderr, "pthread_join: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
	printf("Parent process sees x=%d\n", x);

	return EXIT_SUCCESS;
}
// \end{snippet}
