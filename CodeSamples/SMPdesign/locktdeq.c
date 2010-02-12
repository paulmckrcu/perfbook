/*
 * locktdeq.c: simple lock-based parallel tandem deq implementation.
 * 	This is similar to lockdeq.c, but expresses the parallel
 * 	implementation in terms of a pair of simple single-lock-based deqs.
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"

/* First do the underlying single-locked deq implementation. */

struct deq {
	struct list_head chain;
} ____cacheline_internodealigned_in_smp;

void init_deq(struct deq *p)
{
	INIT_LIST_HEAD(&p->chain);
}

struct list_head *deq_pop_l(struct deq *p)
{
	struct list_head *e;

	if (list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.prev;
		list_del_init(e);
	}
	return e;
}

void deq_push_l(struct list_head *e, struct deq *p)
{
	list_add_tail(e, &p->chain);
}

struct list_head *deq_pop_r(struct deq *p)
{
	struct list_head *e;

	if (list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.next;
		list_del_init(e);
	}
	return e;
}

void deq_push_r(struct list_head *e, struct deq *p)
{
	list_add(e, &p->chain);
}

/*
 * And now the concurrent implementation, which simply has a pair
 * of deq structures in tandem, feeding each other as needed.
 * This of course requires some way of moving elements from one
 * to the other.  This implementation uses a trivial approach:
 * if a pop finds one empty, pull all elements from the
 * other one.
 * 
 * Each individual deq has its own lock, with the left lock acquired
 * first if both locks are required.
 */

struct pdeq {
	spinlock_t llock;
	struct deq ldeq;
	/* char pad1[CACHE_LINE_SIZE - sizeof(spinlock_t) - sizeof(int)]; */
	spinlock_t rlock ____cacheline_internodealigned_in_smp;
	struct deq rdeq;
};

void init_pdeq(struct pdeq *d)
{
	spin_lock_init(&d->llock);
	init_deq(&d->ldeq);
	spin_lock_init(&d->rlock);
	init_deq(&d->rdeq);
}

struct list_head *pdeq_pop_l(struct pdeq *d)
{
	struct list_head *e;
	int i;

	spin_lock(&d->llock);
	e = deq_pop_l(&d->ldeq);
	if (e == NULL) {
		spin_lock(&d->rlock);
		e = deq_pop_l(&d->rdeq);
		list_splice_init(&d->rdeq.chain, &d->ldeq.chain);
		spin_unlock(&d->rlock);
	}
	spin_unlock(&d->llock);
	return e;
}

struct list_head *pdeq_pop_r(struct pdeq *d)
{
	struct list_head *e;
	int i;

	spin_lock(&d->rlock);
	e = deq_pop_r(&d->rdeq);
	if (e == NULL) {
		spin_unlock(&d->rlock);
		spin_lock(&d->llock);
		spin_lock(&d->rlock);
		e = deq_pop_r(&d->rdeq);
		if (e == NULL) {
			e = deq_pop_r(&d->ldeq);
			list_splice_init(&d->ldeq.chain, &d->rdeq.chain);
		}
		spin_unlock(&d->llock);
	}
	spin_unlock(&d->rlock);
	return e;
}

void pdeq_push_l(struct list_head *e, struct pdeq *d)
{
	int i;

	spin_lock(&d->llock);
	deq_push_l(e, &d->ldeq);
	spin_unlock(&d->llock);
}

void pdeq_push_r(struct list_head *e, struct pdeq *d)
{
	int i;

	spin_lock(&d->rlock);
	deq_push_r(e, &d->rdeq);
	spin_unlock(&d->rlock);
}

#ifdef TEST
#include "deqtorture.h"
#endif /* #ifdef TEST */
