/*
 * Functionality for hazard pointers, aka safe memory reclamation (SMR).
 *
 * Uses a linked list for the hazard poitners. Using an array can be a 
 * related experiment.
 *
 * Follows the pseudocode given in :
 *  M. M. Michael. Hazard Pointers: Safe Memory Reclamation for Lock-Free 
 *  Objects. IEEE TPDS (2004) IEEE Transactions on Parallel and Distributed 
 *  Systems 15(8), August 2004.
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
 * Copyright (c) Thomas E. Hart.
 * Copyright (c) 2013 Paul E. McKenney: Updated for perfbook use.
 */
 
#ifndef __HAZPTR_H
#define __HAZPTR_H

#include "../api.h"

/* Parameters to the algorithm:
 *  K: Number of hazard pointers per thread.
 *  H: Number of hazard pointers required.
 *  R: Chosen such that R = H + Omega(H).
 */
#define K 2
#define H (K * NR_THREADS)
#define R (100 + 2*H)

/* Must be the first field in the hazard-pointer-protected structure. */
/* It is illegal to nest one such structure inside another. */
typedef struct hazptr_head {
	struct hazptr_head *next;
} hazptr_head_t;

typedef struct hazard_pointer_s {
	hazptr_head_t *  __attribute__ ((__aligned__ (CACHE_LINE_SIZE))) p;
} hazard_pointer;

/* Must be dynamically initialized to be an array of size H. */
hazard_pointer *HP;
 
void hazptr_init(void);
void hazptr_thread_exit(void);
void hazptr_scan();
void hazptr_free_later(hazptr_head_t *);
void hazptr_free(void *ptr); /* supplied by caller. */

static inline void *hp_record(void **p, hazard_pointer *hp)
{
	hazptr_head_t *tmp;

	do {
		tmp = READ_ONCE(*p);
		WRITE_ONCE(hp->p, tmp);
		smp_mb();
	} while (tmp != READ_ONCE(*p));
	return tmp;
}

static inline void hp_clear(hazard_pointer *hp)
{
	smp_mb();
	WRITE_ONCE(hp->p, NULL);
}

#define hazptr_clean_pointer(p) ((typeof(p))((unsigned long)(p) & ~0x1UL))

#define HAZPTR_POISON 0x8
 
#endif /* #ifndef __HAZPTR_H */
