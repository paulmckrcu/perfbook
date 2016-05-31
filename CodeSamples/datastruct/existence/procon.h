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
 * Note that allocating must be single-threaded.
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
struct procon_mpool __thread *type##__procon_mpool_rcu_cb; \
\
struct type##__procon_mpool_rcu_cb_setup { \
	struct procon_mpool *rcs_mpool; \
	struct rcu_head rcs_rh; \
} __thread type##__procon_mpool_rcu_cb_setup; \
\
void type##__procon_mpool_setup_cb(struct rcu_head *rhp) \
{ \
	struct type##__procon_mpool_rcu_cb_setup *rp; \
	\
	rp = container_of(rhp, struct type##__procon_mpool_rcu_cb_setup, \
			  rcs_rh); \
	type##__procon_mpool_rcu_cb = rp->rcs_mpool; \
} \
\
static inline void type##__procon_init(void) \
{ \
	type##__procon_mpool.pm_tail = &type##__procon_mpool.pm_head; \
	type##__procon_mpool_rcu_cb_setup.rcs_mpool = &type##__procon_mpool; \
	call_rcu(&type##__procon_mpool_rcu_cb_setup.rcs_rh, \
		 type##__procon_mpool_setup_cb); \
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
static inline void type##__procon_free(struct type *p) \
{ \
	procon_free(type##__procon_mpool_rcu_cb, &p->field); \
}

#endif /* #ifndef PROCON_H */
