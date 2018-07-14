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
 * Copyright (c) Thomas E. Hart.
 * Copyright (c) 2013 Paul E. McKenney: Updated for perfbook use.
 */

#include "hazptr.h"
#include <stdio.h>
#include <stdlib.h>

static hazptr_head_t __thread *rlist;
static unsigned long __thread rcount;
static hazptr_head_t __thread **gplist;

void hazptr_init(void)
{
	int i;

	/* Allocate HP array. */
	HP = (hazard_pointer *)malloc(sizeof(hazard_pointer) * K * NR_THREADS);
	if (HP == NULL) {
		fprintf(stderr, "SMR hazptr_init: out of memory\n");
		exit(EXIT_FAILURE);
	}

	/* Initialize the hazard pointers. */
	for (i = 0; i < K * NR_THREADS; i++)
		HP[i].p = NULL;
}

void hazptr_thread_exit(void)
{
	unsigned long myTID = smp_thread_id();
	int i;

	for (i = 0; i < K; i++)
		HP[K*myTID+i].p = NULL;
	
	while (rcount > 0) {
		hazptr_scan();
		poll(NULL, 0, 1);
	}
}

void hazptr_reinitialize()
{
}

/* 
 * Comparison function for qsort.
 *
 * We just need any total order, so we'll use the arithmetic order 
 * of pointers on the machine.
 *
 * Output (see "man qsort"):
 *  < 0 : a < b
 *    0 : a == b
 *  > 0 : a > b
 */
int compare (const void *a, const void *b)
{
  return ( *(hazptr_head_t **)a - *(hazptr_head_t **)b );
}

/* Debugging function. Leave it around. */
inline hazptr_head_t *ssearch(hazptr_head_t **list, int size, hazptr_head_t *key) {
	int i;
	for (i = 0; i < size; i++)
		if (list[i] == key)
			return list[i];
	return NULL;
}

void hazptr_scan()
{
	/* Iteratation variables. */
	hazptr_head_t *cur;
	int i;

	/* List of SMR callbacks. */
	hazptr_head_t *tmplist;

	/* List of hazard pointers, and its size. */
	hazptr_head_t **plist = gplist;
	unsigned long psize;

	if (plist == NULL) {
		plist = (hazptr_head_t **)malloc(sizeof(hazptr_head_t *) * K * NR_THREADS);
		if (plist == NULL) {
			fprintf(stderr, "hazptr_scan: out of memory\n");
			exit(EXIT_FAILURE);
		}
	}

	/*
	 * Make sure that the most recent node to be deleted has been unlinked
	 * in all processors' views.
	 *
	 * Good:
	 *   A -> B -> C ---> A -> C ---> A -> C
	 *                    B -> C      B -> POISON
	 *
	 * Illegal:
	 *   A -> B -> C ---> A -> B      ---> A -> C
	 *                    B -> POISON      B -> POISON
	 */
	smp_mb();

	/* Stage 1: Scan HP list and insert non-null values in plist. */
	psize = 0;
	for (i = 0; i < H; i++) {
		if (HP[i].p == NULL)
			continue;
		plist[psize++] = (hazptr_head_t *)((unsigned long)HP[i].p & ~0x1UL);
	}
	smp_mb(); /* ensure freeing happens after scan. */
	
	/* Stage 2: Sort the plist. */
	qsort(plist, psize, sizeof(hazptr_head_t *), compare);

	/* Stage 3: Free non-harzardous nodes. */
	tmplist = rlist;
	rlist = NULL;
	rcount = 0;
	while (tmplist != NULL) {
		/* Pop cur off top of tmplist. */
		cur = tmplist;
		tmplist = tmplist->next;

		if (bsearch(&cur, plist, psize, sizeof(hazptr_head_t *), compare)) {
			cur->next = rlist;
			rlist = cur;
			rcount++;
		} else {
			hazptr_free(cur);
		}
	}
}

void hazptr_free_later(hazptr_head_t *n)
{
	n->next = rlist;
	rlist = n;
	rcount++;

	if (rcount >= R) {
		hazptr_scan();
	}
}

#ifdef TEST
#include "hazptrtorture.h"
#endif /* #ifdef TEST */
