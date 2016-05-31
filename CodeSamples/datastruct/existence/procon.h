/*
 * procon.h: Crude producer-consumer memory allocator
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
 * Copyright (c) 2016 Paul E. McKenney, IBM Corporation.
 */

#ifndef PROCON_H
#define PROCON_H

/* Individual memory block */
struct procon_mblock {
	struct procon_mblock *pm_next;
};

/* Producer/consumer memory pool. */
struct procon_mpool {
	struct procon_mblock *pm_head;
	unsigned long pm_alloccount;
	unsigned long pm_outcount;
	unsigned long pm_unoutcount;
	struct procon_mblock *(*pm_alloc)(void);
	struct procon_mblock **pm_tail
			__attribute__((__aligned__(CACHE_LINE_SIZE)));
	unsigned long pm_incount;
};

/*
 * Remove a block from the pool, or get one from the allocator
 * if the pool is low on blocks.  NULL if no memory to be had.
 * Note that allocating and unallocating must be single-threaded.
 */
static inline struct procon_mblock *procon_alloc(struct procon_mpool *pmp)
{
	struct procon_mblock *pmbp = pmp->pm_head;

	if (pmbp == NULL || ACCESS_ONCE(pmbp->pm_next) == NULL) {
		pmp->pm_alloccount++;
		return pmp->pm_alloc();
	}
	pmp->pm_outcount++;
	pmp->pm_head = pmbp->pm_next;
	return pmbp;
}

/*
 * Push a newly allocated block back to the pool.  This may be carried out
 * by the allocating thread, but only if the block has not yet been exposed
 * to RCU readers.
 */
void procon_unalloc(struct procon_mpool *pmp, struct procon_mblock *pmbp)
{
	/* @@@ */
}

/*
 * Add a block to the pool.  Note that freeing must be single-threaded.
 */
void procon_free(struct procon_mpool *pmp, struct procon_mblock *pmbp)
{
	struct procon_mblock **nextp;

	nextp = pmp->pm_tail;
	pmp->pm_tail = &pmbp->pm_next;
	ACCESS_ONCE(*nextp) = pmbp;
	pmp->pm_incount++;
}

#define DEFINE_PROCON_MPOOL(type, field, alloc) \
static inline struct procon_mblock *type##__alloc(void) \
{ \
	struct type *p = (alloc); \
	\
	if (p == NULL) \
		return NULL; \
	return &p->field; \
} \
\
struct procon_mpool __thread type##__procon_mpool = { \
	.pm_alloc = type##__alloc, \
}; \
\
static inline void type##__procon_init(struct procon_mpool *pmp) \
{ \
	pmp->pm_tail = &pmp->pm_head; \
} \
\
static inline struct type *type##__procon_alloc(void) \
{ \
	struct procon_mblock *p; \
	\
	p = procon_alloc(&type##__procon_mpool); \
	return container_of(p, struct type, field); \
} \
\
static inline void type##__procon_free(struct procon_mpool *pmp, \
				       struct type *p) \
{ \
	procon_free(pmp, &p->field); \
}

#endif /* #ifndef PROCON_H */
