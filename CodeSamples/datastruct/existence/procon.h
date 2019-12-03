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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
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
	struct procon_mblock *pm_unalloc;
	unsigned long pm_alloccount;
	unsigned long pm_outcount;
	unsigned long pm_unoutcount;
	struct procon_mblock *(*pm_alloc)(void);
	struct procon_mblock **pm_tail
			__attribute__((__aligned__(CACHE_LINE_SIZE)));
	unsigned long pm_incount;
	struct rcu_head pm_rh;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

/* Statistics reporting structure. */
struct procon_stats {
	unsigned long pm_alloccount;
	unsigned long pm_outcount;
	unsigned long pm_unoutcount;
	unsigned long pm_incount;
};

/* Thread-local buffering to reduce free-side cache misses. */
#define PROCON_MAX_BUF 128
struct procon_buf {
	struct procon_mblock *pb_head;
	struct procon_mblock **pb_tail;
	unsigned long pb_count;
};

/*
 * Remove a block from the pool, or get one from the allocator
 * if the pool is low on blocks.  NULL if no memory to be had.
 * Note that allocating and unallocating must be single-threaded.
 */
static inline struct procon_mblock *procon_alloc(struct procon_mpool *pmp)
{
	struct procon_mblock *pmbp = pmp->pm_head;

	if ((pmbp == NULL || ACCESS_ONCE(pmbp->pm_next) == NULL) &&
	    pmp->pm_unalloc == NULL) {
		pmp->pm_alloccount++;
		return pmp->pm_alloc();
	}
	pmp->pm_outcount++;
	if (pmp->pm_unalloc != NULL) {
		pmbp = pmp->pm_unalloc;
		pmp->pm_unalloc = pmbp->pm_next;
	} else {
		pmp->pm_head = pmbp->pm_next;
	}
	pmbp->pm_next = NULL;
	return pmbp;
}

/*
 * Push a block back onto the pool.  Note that the block must not yet have
 * been exposed to readers and that this must be single-threaded from
 * the allocation side.
 */
void procon_unalloc(struct procon_mpool *pmp, struct procon_mblock *pmbp)
{
	pmbp->pm_next = pmp->pm_unalloc;
	pmp->pm_unalloc = pmbp;
	pmp->pm_unoutcount++;
}

/*
 * Add a block to the pool.  Note that freeing must be single-threaded.
 */
void procon_free(struct procon_mpool *pmp, struct procon_mblock *pmbp,
		 struct procon_buf *pbp)
{
	struct procon_mblock **oldtail;

	/* Add to the local buffer. */
	if (!pbp->pb_tail)
		pbp->pb_tail = &pbp->pb_head;
	oldtail = pbp->pb_tail;
	pbp->pb_tail = &pmbp->pm_next;
	*oldtail = pmbp;
	if (++pbp->pb_count < PROCON_MAX_BUF)
		return;

	/* The local buffer is full, pass it on to the consumer. */
	oldtail = __atomic_exchange_n(&pmp->pm_tail, pbp->pb_tail,
				      __ATOMIC_SEQ_CST);
	ACCESS_ONCE(*oldtail) = pbp->pb_head;
	__atomic_fetch_add(&pmp->pm_incount, pbp->pb_count, __ATOMIC_RELAXED);
	pbp->pb_head = NULL;
	pbp->pb_tail = &pbp->pb_head;
	pbp->pb_count = 0;
}

/*
 * Sum procon_stats structure into a total-accumulation structure.
 */
void procon_stats_accumulate(struct procon_stats *ps, struct procon_stats *p)
{
	ps->pm_alloccount += p->pm_alloccount;
	ps->pm_outcount += p->pm_outcount;
	ps->pm_unoutcount += p->pm_unoutcount;
	ps->pm_incount += p->pm_incount;
}

/*
 * Print out procon_stats structure.
 */
void procon_stats_print(struct procon_stats *p)
{
	printf("\tpm_alloccount = %lu\n", p->pm_alloccount);
	printf("\tpm_outcount = %lu\n", p->pm_outcount);
	printf("\tpm_unoutcount = %lu\n", p->pm_unoutcount);
	printf("\tpm_incount = %lu\n", p->pm_incount);
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
struct procon_mpool __thread type##__procon_mpool_backing = { \
	.pm_alloc = type##__alloc, \
}; \
struct procon_mpool __thread *type##__procon_mpool; \
struct procon_buf __thread type##__procon_buf; \
\
void type##__procon_mpool_setup_cb(struct rcu_head *rhp) \
{ \
	struct procon_mpool *pmp; \
	\
	pmp = container_of(rhp, struct procon_mpool, pm_rh); \
	type##__procon_mpool = pmp; \
} \
\
static inline void type##__procon_init(void) \
{ \
	type##__procon_mpool_backing.pm_tail = \
		&type##__procon_mpool_backing.pm_head; \
	type##__procon_mpool = &type##__procon_mpool_backing; \
	call_rcu(&type##__procon_mpool_backing.pm_rh, \
		 type##__procon_mpool_setup_cb); \
} \
\
static inline struct type *type##__procon_alloc(void) \
{ \
	struct procon_mblock *p; \
	\
	p = procon_alloc(&type##__procon_mpool_backing); \
	if (p == NULL) \
		return NULL; \
	return container_of(p, struct type, field); \
} \
\
static inline void type##__procon_unalloc(struct type *p) \
{ \
	procon_unalloc(&type##__procon_mpool_backing, &p->field); \
} \
\
static inline void type##__procon_free(struct type *p) \
{ \
	procon_free(type##__procon_mpool, &p->field, &type##__procon_buf); \
} \
\
static inline void type##__procon_stats(struct procon_stats *psp) \
{ \
	psp->pm_alloccount = type##__procon_mpool_backing.pm_alloccount; \
	psp->pm_outcount = type##__procon_mpool_backing.pm_outcount; \
	psp->pm_unoutcount = type##__procon_mpool_backing.pm_unoutcount; \
	psp->pm_incount = type##__procon_mpool_backing.pm_incount; \
}

#endif /* #ifndef PROCON_H */
