/*
 * HTMovf.c: Combinatorial computation of cache-overflow probability
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
 * Copyright (c) 2012-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include <stdio.h>
#include <stdlib.h>

int assoc;	/* Cache associativity. */
int nrefs;	/* Number of references. */
int nsets;	/* Cache sets.  # cache lines is assoc*nsets. */

/*
 * Count one overflow case.
 */
int n_ovf;
void count_pattern(int *base, int *lim)
{
	n_ovf++;
}

/* 
 * Output the maxima computations for one overflow case.
 */
void output_pattern(int *base, int *lim)
{
	int i;
	int last;
	int m = 0;
	int n = lim - base + 1;
	int *sp;

	last = *base;
	for (sp = base; sp <= lim; sp++) {
		m += *sp;
		if (*sp > last)
			abort();
		last = *sp;
	}
	if (m != nrefs)
		abort();
	printf("bfloat(s:s+((%d!/(", n);
	i = 0;
	last = *base;
	for (sp = base; sp <= lim; sp++) {
		if (*sp == last)
			i++;
		else {
			if (i > 0)
				printf("%d!*", i);
			i = 1;
			last = *sp;
		}
	}
	printf("%d!))*(%d!/(", i, m);
	for (sp = base; sp <= lim; sp++)
		if (*sp > 1)
			printf("%d!*", *sp);
	printf("1))/%d^%d));\n", n, m);
}

/*
 * Enumerate possible failure-inducing spreadings of sets for arrivals.
 * Start with all references hitting one set, then incrementally spread
 * into all unique patterns over permutations of the sets.
 */
void spread_failure(void (*report_pattern)(int *base, int *lim),
		    int *base, int *lb, int *next, int *lim, int assoc)
{
	if (*base > assoc)
		report_pattern(base, lim);
	else
		return;  /* Further spreading will fit into cache. */
	for (;;) {
		(*base)--;
		(*next)++;
		if (*next > *lb || *base < *(base + 1) || *base <= assoc)
			break;
		if (next < lim)
			spread_failure(report_pattern,
				       base, next, next + 1, lim, assoc);
		else if (*base > assoc)
			report_pattern(base, lim);
	}
	*base += *next;
	*next = 0;
}

/*
 * Enumerate possible successful spreadings of sets for arrivals.
 * Start with all references filling the maximum number of sets that
 * that number of references can cover, then incrementally spread
 * into all unique patterns over permutations of the sets.
 */
int spread_success(void (*report_pattern)(int *base, int *lim),
		   int *base, int *next, int *lim, int max, int n)
{
	int i;

	if (n < max) {
		*next = n;
		report_pattern(base, lim);
		if (next == lim) {
			*next = 0;
			return 1;
		}
		i = n - 1;
	} else {
		*next = max;
		if (n == max)
			report_pattern(base, lim);
		if (next == lim) {
			*next = 0;
			return 1;
		}
		if (n > max &&
		    !spread_success(report_pattern,
		    		    base, next + 1, lim, max, n - max)) {
			*next = 0;
			return 0;
		}
		i = max - 1;
	}
	for (; i > 0; i--) {
		*next = i;
		if (!spread_success(report_pattern,
				    base, next + 1, lim, i, n - i)) {
			*next = 0;
			return 1;
		}
	}
	*next = 0;
	return 1;
}

void do_failure(void (*report_pattern)(int *base, int *lim), int *s)
{
	int i;

	s[0] = nrefs;
	for (i = 1; i < nsets; i++)
		s[i] = 0;
	spread_failure(report_pattern, s, s, &s[1], &s[nsets - 1], assoc);
}

void do_success(void (*report_pattern)(int *base, int *lim), int *s)
{
	int i;

	for (i = 0; i < nsets; i++)
		s[i] = 0;
	spread_success(report_pattern, s, s, &s[nsets - 1], assoc, nrefs);
}

void compute_failure(int *s)
{
	printf("s:0;\n");
	do_failure(output_pattern, s);
}

void compute_success(int *s)
{
	printf("s:0;\n");
	do_success(output_pattern, s);
}

void usage(char *argv[])
{
	fprintf(stderr, "Usage: %s [ c C f p s] nsets assoc nrefs\n", argv[0]);
	fprintf(stderr, "\tc: Check success vs. failure computation.\n");
	fprintf(stderr, "\tC: Check success vs. failure # patterns.\n");
	fprintf(stderr, "\tf: Compute p(failure).\n");
	fprintf(stderr, "\tp: Compute p(failure) by most efficient means.\n");
	fprintf(stderr, "\ts: Compute p(success).\n");
	exit(-1);
}

int main(int argc, char *argv[])
{
	int *s;

	if (argc != 5) {
		usage(argv);
	}
	nsets = atoi(argv[2]);
	assoc = atoi(argv[3]);
	nrefs = atoi(argv[4]);
	s = malloc(nsets * sizeof(s[0]));
	if (s == NULL)
		abort();
	if (argv[1][0] == 'c') {
		compute_failure(s);
		printf("bfloat(q:s);\n");
		compute_success(s);
		printf("bfloat(p:s);\n");
		printf("print(\"@@@ p = \", bfloat(p), \" q = \", bfloat(q), \"p + q = \", bfloat(p + q));\n");
	} else if (argv[1][0] == 'C') {
		int nf;
		int ns;

		n_ovf = 0;
		do_failure(count_pattern, s);
		nf = n_ovf;
		n_ovf = 0;
		do_success(count_pattern, s);
		ns = n_ovf;
		printf("# non-overflow patterns: %d\n", ns);
		printf("# overflow patterns: %d\n", nf);
	} else if (argv[1][0] == 'f') {
		compute_failure(s);
		printf("print(\"@@@ p(failure) = \", bfloat(s));\n");
	} else if (argv[1][0] == 'p') {
		int nf;
		int ns;

		n_ovf = 0;
		do_failure(count_pattern, s);
		nf = n_ovf;
		n_ovf = 0;
		do_success(count_pattern, s);
		ns = n_ovf;
		if (nf < ns) {
			compute_failure(s);
			printf("print(\"@@@ p(failure) = \", bfloat(s));\n");
		} else {
			compute_success(s);
			printf("print(\"@@@ p(failure) = \", bfloat(1-s));\n");
		}
	} else if (argv[1][0] == 's') {
		compute_success(s);
		printf("print(\"@@@ p(success) = \", bfloat(s));\n");
	} else
		usage(argv);
	return 0;
}
