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
		WRITE_ONCE(HP[K*myTID+i].p, NULL);
	
	while (rcount > 0) {
		hazptr_scan();
		poll(NULL, 0, 1);
	}

	free(gplist);
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
//\begin{snippet}[labelbase=ln:defer:hazptr:scan_free,gobbleblank=yes,commandchars=\%\@\$]
int compare(const void *a, const void *b)
{
	return ( *(hazptr_head_t **)a - *(hazptr_head_t **)b );
}
							//\fcvblank
void hazptr_scan()				//\lnlbl{scan:b}
{
	/* Iteratation variables. */
	hazptr_head_t *cur;
	int i;

	/* List of SMR callbacks. */
	hazptr_head_t *tmplist;

	/* List of hazard pointers, and its size. */
	hazptr_head_t **plist = gplist;
	unsigned long psize;
							//\fcvblank
	if (plist == NULL) {			//\lnlbl{scan:check}
		psize = sizeof(hazptr_head_t *) * K * NR_THREADS; //\lnlbl{scan:alloc:b}
		plist = (hazptr_head_t **)malloc(psize);
		BUG_ON(!plist);
		gplist = plist;			//\lnlbl{scan:alloc:e}
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
	smp_mb();				//\lnlbl{scan:mb1}

	/* Stage 1: Scan HP list and insert non-null values in plist. */
	psize = 0;
	for (i = 0; i < H; i++) {		//\lnlbl{scan:loop:b}
		uintptr_t hp = (uintptr_t)READ_ONCE(HP[i].p);
							//\fcvblank
		if (!hp)
			continue;
		plist[psize++] = (hazptr_head_t *)(hp & ~0x1UL);
	}					//\lnlbl{scan:loop:e}
	smp_mb(); /* ensure freeing happens after scan. */ //\lnlbl{scan:mb2}
	
	/* Stage 2: Sort the plist. */
	qsort(plist, psize, sizeof(hazptr_head_t *), compare); //\lnlbl{scan:sort}

	/* Stage 3: Free non-harzardous nodes. */
	tmplist = rlist;			//\lnlbl{scan:rem:b}
	rlist = NULL;				//\lnlbl{scan:rem:e}
	rcount = 0;				//\lnlbl{scan:zero}
	while (tmplist != NULL) {		//\lnlbl{scan:loop2:b}
		/* Pop cur off top of tmplist. */
		cur = tmplist;			//\lnlbl{scan:rem1st:b}
		tmplist = tmplist->next;	//\lnlbl{scan:rem1st:e}

		if (bsearch(&cur, plist, psize,	//\lnlbl{scan:chkhazp:b}
		            sizeof(hazptr_head_t *), compare)) { //\lnlbl{scan:chkhazp:e}
			cur->next = rlist;	//\lnlbl{scan:back:b}
			rlist = cur;
			rcount++;		//\lnlbl{scan:back:e}
		} else {
			hazptr_free(cur);	//\lnlbl{scan:free}
		}
	}					//\lnlbl{scan:loop2:e}
}						//\lnlbl{scan:e}
							//\fcvblank
void hazptr_free_later(hazptr_head_t *n)	//\lnlbl{free:b}
{
	n->next = rlist;			//\lnlbl{free:enq:b}
	rlist = n;				//\lnlbl{free:enq:e}
	rcount++;				//\lnlbl{free:count}

	if (rcount >= R) {			//\lnlbl{free:check}
		hazptr_scan();			//\lnlbl{free:scan}
	}
}						//\lnlbl{free:e}
//\end{snippet}
#ifdef TEST
#include "hazptrtorture.h"
#endif /* #ifdef TEST */
