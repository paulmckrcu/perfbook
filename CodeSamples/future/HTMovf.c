#include <stdio.h>
#include <stdlib.h>

int assoc;
int nrefs;
int nsets;

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

void compute_failure(int *s)
{
	int i;

	s[0] = nrefs;
	for (i = 1; i < nsets; i++)
		s[i] = 0;
	printf("s:0;\n");
	spread_failure(output_pattern, s, s, &s[1], &s[nsets - 1], assoc);
}

void compute_success(int *s)
{
	int i;

	printf("s:0;\n");
	for (i = 0; i < nsets; i++)
		s[i] = 0;
	spread_success(output_pattern, s, s, &s[nsets - 1], assoc, nrefs);
}

int main(int argc, char *argv[])
{
	int *s;

	if (argc != 4) {
		fprintf(stderr, "Usage: %s nsets assoc nrefs\n", argv[0]);
		exit(-1);
	}
	nsets = atoi(argv[1]);
	assoc = atoi(argv[2]);
	nrefs = atoi(argv[3]);
	s = malloc(nsets * sizeof(s[0]));
	if (s == NULL)
		abort();
	compute_failure(s);
	printf("bfloat(q:s);\n");
	compute_success(s);
	printf("bfloat(p:s);\n");
	printf("print(\"@@@ p = \", bfloat(p), \" q = \", bfloat(q), \"p + q = \", bfloat(p + q));\n");
}
