/*
 * matmul.c: multiply a pair of matrices.
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

#include "../api.h"

float *a;
float *b;
float *c;
float *d;
long dim = 1000;
int nthread = 1;

#define GOFLAG_INIT     0
#define GOFLAG_START    1
#define GOFLAG_STOP     2

int goflag;
atomic_t ndone;
atomic_t nstarted;

#define IDX(i, j) ((i) * dim + (j))

void *matmul_thread(void *me_in)
{
	long blocksize = (dim + nthread - 1) / nthread;
	long me = (intptr_t)me_in;
	int i, j, k;
	long startidx = me * blocksize;
	long stopidx = startidx + blocksize;

	if (stopidx > dim)
		stopidx = dim;
	atomic_inc(&nstarted);
	while (goflag == GOFLAG_INIT)
		barrier();

	for (i = startidx; i < stopidx; i++)
		for (j = 0; j < dim; j++) {
			c[IDX(i, j)] = 0.;
			for (k = 0; k < dim; k++)
				c[IDX(i, j)] += a[IDX(i, k)] * b[IDX(k, j)];
		}

	atomic_inc(&ndone);
	return NULL;
}

int main(int argc, char *argv[])
{
	int i, j, k;
	long long startcreatetime;
	long long endpartime;
	long long endtime;

	if (argc >= 2)
		dim = strtol(argv[1], NULL, 0);
	if (argc >= 3)
		nthread = strtol(argv[2], NULL, 0);

	atomic_set(&nstarted, 0);
	atomic_set(&ndone, 0);
	a = malloc(sizeof(a[0]) * dim * dim);
	b = malloc(sizeof(b[0]) * dim * dim);
	c = malloc(sizeof(c[0]) * dim * dim);
	d = malloc(sizeof(c[0]) * dim * dim);
	if (a == NULL || b == NULL || c == NULL || d == NULL) {
		printf("Out of memory\n");
		exit(EXIT_FAILURE);
	}

	for (i = 0; i < dim; i++)
		for (j = 0; j < dim; j++) {
			a[IDX(i, j)] = (float)(i + j);
			b[IDX(i, j)] = (float)(i * j);
		}

	goflag = GOFLAG_INIT;
	startcreatetime = get_microseconds();
	for (i = 0; i < nthread; i++)
		create_thread(matmul_thread, (void *)(intptr_t)i);
	while (atomic_read(&nstarted) != nthread)
		barrier();
	goflag = GOFLAG_START;
	while (atomic_read(&ndone) != nthread)
		poll(NULL, 0, 1);
	endpartime = get_microseconds();
	for (i = 0; i < dim; i++)
		for (j = 0; j < dim; j++) {
			d[IDX(i, j)] = 0.;
			for (k = 0; k < dim; k++)
				d[IDX(i, j)] += a[IDX(i, k)] * b[IDX(k, j)];
		}
	endtime = get_microseconds();
	for (i = 0; i < dim; i++)
		for (j = 0; j < dim; j++)
			BUG_ON(c[IDX(i, j)] != d[IDX(i, j)]);
	printf("dim = %ld, nthread = %d, duration = %lld : %lld us\n",
	       dim, nthread, endpartime - startcreatetime, endtime - endpartime);
	return EXIT_SUCCESS;
}
