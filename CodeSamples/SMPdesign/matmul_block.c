/*
 * matmul_block.c: multiply a pair of matrices, blocking for cache lines.
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
long dim = 1000;
int nthread = 1;

#define GOFLAG_INIT     0
#define GOFLAG_START    1
#define GOFLAG_STOP     2

int goflag;
atomic_t ndone;
atomic_t nstarted;

#define IDX(i, j) ((i) * dim + (j))

struct band {
	int first;
	int last;
};

void *matmul_thread(void *band_in)
{
	struct band *myband = band_in;
	int i, j, k;

	atomic_inc(&nstarted);
	while (goflag == GOFLAG_INIT)
		barrier();

	for (i = myband->first; i < myband->last; i++)
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
	int i, j;
	struct band *bands;
	int bandsize;
	long long startcreatetime;
	long long starttime;
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
	bands = malloc(sizeof(bands[0]) * nthread);
	if (a == NULL || b == NULL || c == NULL || bands == NULL) {
		printf("Out of memory\n");
		exit(EXIT_FAILURE);
	}
	for (i = 0; i < dim; i++)
		for (j = 0; j < dim; j++) {
			a[IDX(i, j)] = (float)(i + j);
			b[IDX(i, j)] = (float)(i * j);
		}

	goflag = GOFLAG_INIT;
	bandsize = (dim + nthread - 1) / nthread;
	startcreatetime = get_microseconds();
	for (i = 0; i < nthread; i++) {
		bands[i].first = bandsize * nthread;
		bands[i].last = bandsize * (nthread + 1) - 1;
		if (i == nthread - 1)
			bands[i].last = dim - 1;
		create_thread(matmul_thread, (void *)&bands[i]);
	}
	while (atomic_read(&nstarted) != nthread)
		barrier();
	starttime = get_microseconds();
	goflag = GOFLAG_START;
	while (atomic_read(&ndone) != nthread)
		poll(NULL, 0, 1);
	endtime = get_microseconds();
	printf("dim = %ld, nthread = %d, duration = %lld : %lld us\n",
	       dim, nthread, endtime - startcreatetime, endtime - starttime);
	return EXIT_SUCCESS;
}
