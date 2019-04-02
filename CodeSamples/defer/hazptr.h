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
	void *  __attribute__ ((__aligned__ (CACHE_LINE_SIZE))) p;
} hazard_pointer;

/* Must be dynamically initialized to be an array of size H. */
hazard_pointer *HP;
 
void hazptr_init(void);
void hazptr_thread_exit(void);
void hazptr_scan();
void hazptr_free_later(hazptr_head_t *);
void hazptr_free(void *ptr); /* supplied by caller. */

#define HAZPTR_POISON 0x8

/* This can be used when reading a pointer from an immortal structure. */
//\begin{snippet}[labelbase=ln:defer:hazptr:record_clear,commandchars=\\\[\]]
static inline void *_h_t_r_impl(void **p,		//\lnlbl{htr:b}
                                hazard_pointer *hp)
{
	void *tmp;

	tmp = READ_ONCE(*p);				//\lnlbl{htr:ro1}
	if (!tmp || tmp == (void *)HAZPTR_POISON)
		return tmp;				//\lnlbl{htr:race1}
	WRITE_ONCE(hp->p, tmp);				//\lnlbl{htr:store}
	smp_mb();					//\lnlbl{htr:mb}
	if (tmp == READ_ONCE(*p))			//\lnlbl{htr:ro2}
		return tmp;				//\lnlbl{htr:success}
	return (void *)HAZPTR_POISON;			//\lnlbl{htr:race2}
}

#define hp_try_record(p, hp) _h_t_r_impl((void **)(p), hp) //\lnlbl{htr:e}

static inline void *hp_record(void **p,			//\lnlbl{hr:b}
                              hazard_pointer *hp)
{
	void *tmp;

	do {
		tmp = hp_try_record(*p, hp);
	} while (tmp == (void *)HAZPTR_POISON);
	return tmp;
}							//\lnlbl{hr:e}

static inline void hp_clear(hazard_pointer *hp)		//\lnlbl{hc:b}
{
	smp_mb();
	WRITE_ONCE(hp->p, NULL);
}							//\lnlbl{hc:e}
//\end{snippet}

#define hazptr_clean_pointer(p) ((typeof(p))((unsigned long)(p) & ~0x1UL))
 
#endif /* #ifndef __HAZPTR_H */
