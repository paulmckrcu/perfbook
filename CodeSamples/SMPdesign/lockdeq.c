/*
 * lockdeq.c: simple lock-based parallel deq implementation.
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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

/*
 * Deq structure, empty list:
 *
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *     |   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *                               ^   ^
 *                               |   |
 *                            lidx   ridx
 *
 *
 * List after three deq_push_l() invocations of "a", "b", and "c":
 *
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *     |   |   |   |   | c | b | a |   |   |   |   |   |   |   |   |
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *                   ^               ^
 *                   |               |
 *                lidx               ridx
 *
 * List after one deq_pop_r() invocations (removing "a"):
 *
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *     |   |   |   |   | c | b |   |   |   |   |   |   |   |   |   |
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *                   ^           ^
 *                   |           |
 *                lidx           ridx
 *
 * This is pretty standard.  The trick is that only the low-order bits
 * of lidx and ridx are used to index into a power-of-two sized hash
 * table.  Each bucket of the hash table is a circular doubly linked
 * list (AKA liburcu cds_list_head structure).  Left-hand operations
 * manipulate the tail of the selected list, while right-hand operations
 * manipulate the head of the selected list.  Each bucket has its own
 * lock, minimizing lock contention.  Each of the two indexes also has
 * its own lock.
 */

/*
 * This must be a power of two.  If you want something else, also adjust
 * the moveleft() and moveright() functions.
 */
#define DEQ_N_BKTS 4

struct deq_bkt {
	spinlock_t lock;
	struct cds_list_head chain;
} ____cacheline_internodealigned_in_smp;

struct pdeq {
	spinlock_t llock;
	int lidx;
	/* char pad1[CACHE_LINE_SIZE - sizeof(spinlock_t) - sizeof(int)]; */
	spinlock_t rlock ____cacheline_internodealigned_in_smp;
	int ridx;
	/* char pad2[CACHE_LINE_SIZE - sizeof(spinlock_t) - sizeof(int)]; */
	struct deq_bkt bkt[DEQ_N_BKTS];
};

static int moveleft(int idx)
{
	return (idx - 1) & (DEQ_N_BKTS - 1);
}

static int moveright(int idx)
{
	return (idx + 1) & (DEQ_N_BKTS - 1);
}

void init_pdeq(struct pdeq *d)
{
	int i;

	d->lidx = 0;
	spin_lock_init(&d->llock);
	d->ridx = 1;
	spin_lock_init(&d->rlock);
	for (i = 0; i < DEQ_N_BKTS; i++) {
		spin_lock_init(&d->bkt[i].lock);
		CDS_INIT_LIST_HEAD(&d->bkt[i].chain);
	}
}

struct cds_list_head *pdeq_pop_l(struct pdeq *d)
{
	struct cds_list_head *e;
	int i;
	struct deq_bkt *p;

	spin_lock(&d->llock);
	i = moveright(d->lidx);
	p = &d->bkt[i];
	spin_lock(&p->lock);
	if (cds_list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.prev;
		cds_list_del(e);
		CDS_INIT_LIST_HEAD(e);
		d->lidx = i;
	}
	spin_unlock(&p->lock);
	spin_unlock(&d->llock);
	return e;
}

struct cds_list_head *pdeq_pop_r(struct pdeq *d)
{
	struct cds_list_head *e;
	int i;
	struct deq_bkt *p;

	spin_lock(&d->rlock);
	i = moveleft(d->ridx);
	p = &d->bkt[i];
	spin_lock(&p->lock);
	if (cds_list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.next;
		cds_list_del(e);
		CDS_INIT_LIST_HEAD(e);
		d->ridx = i;
	}
	spin_unlock(&p->lock);
	spin_unlock(&d->rlock);
	return e;
}

void pdeq_push_l(struct cds_list_head *e, struct pdeq *d)
{
	int i;
	struct deq_bkt *p;

	spin_lock(&d->llock);
	i = d->lidx;
	p = &d->bkt[i];
	spin_lock(&p->lock);
	cds_list_add_tail(e, &p->chain);
	d->lidx = moveleft(d->lidx);
	spin_unlock(&p->lock);
	spin_unlock(&d->llock);
}

void pdeq_push_r(struct cds_list_head *e, struct pdeq *d)
{
	int i;
	struct deq_bkt *p;

	spin_lock(&d->rlock);
	i = d->ridx;
	p = &d->bkt[i];
	spin_lock(&p->lock);
	cds_list_add(e, &p->chain);
	d->ridx = moveright(d->ridx);
	spin_unlock(&p->lock);
	spin_unlock(&d->rlock);
}

#ifdef TEST
#include "deqtorture.h"
#endif /* #ifdef TEST */
