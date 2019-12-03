/*
 * lockhdeq.c: simple lock-based parallel hashed deq implementation.
 * 	This is similar to lockdeq.c, but expresses the parallel
 * 	implementation in terms of a simple single-lock-based deq.
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

/* First do the underlying single-locked deq implementation. */

struct deq {
	spinlock_t lock;
	struct cds_list_head chain;
} ____cacheline_internodealigned_in_smp;

void init_deq(struct deq *p)
{
	spin_lock_init(&p->lock);
	CDS_INIT_LIST_HEAD(&p->chain);
}

struct cds_list_head *deq_pop_l(struct deq *p)
{
	struct cds_list_head *e;

	spin_lock(&p->lock);
	if (cds_list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.prev;
		cds_list_del(e);
		CDS_INIT_LIST_HEAD(e);
	}
	spin_unlock(&p->lock);
	return e;
}

void deq_push_l(struct cds_list_head *e, struct deq *p)
{
	spin_lock(&p->lock);
	cds_list_add_tail(e, &p->chain);
	spin_unlock(&p->lock);
}

struct cds_list_head *deq_pop_r(struct deq *p)
{
	struct cds_list_head *e;

	spin_lock(&p->lock);
	if (cds_list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.next;
		cds_list_del(e);
		CDS_INIT_LIST_HEAD(e);
	}
	spin_unlock(&p->lock);
	return e;
}

void deq_push_r(struct cds_list_head *e, struct deq *p)
{
	spin_lock(&p->lock);
	cds_list_add(e, &p->chain);
	spin_unlock(&p->lock);
}

/*
 * And now the concurrent implementation.
 *
 * Pdeq structure, empty list:
 *
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *     |   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *                               ^   ^
 *                               |   |
 *                            lidx   ridx
 *
 *
 * List after three pdeq_push_l() invocations of "a", "b", and "c":
 *
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *     |   |   |   |   | c | b | a |   |   |   |   |   |   |   |   |
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *                   ^               ^
 *                   |               |
 *                lidx               ridx
 *
 * List after one pdeq_pop_r() invocations (removing "a"):
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

#define PDEQ_N_BKTS 4

//\begin{snippet}[labelbase=ln:SMPdesign:lockhdeq:struct_pdeq,commandchars=\\\@\$]
struct pdeq {
	spinlock_t llock;				//\lnlbl{llock}
	int lidx;					//\lnlbl{lidx}
	/* char pad1[CACHE_LINE_SIZE - sizeof(spinlock_t) - sizeof(int)]; */
#ifndef FCV_SNIPPET
	spinlock_t rlock ____cacheline_internodealigned_in_smp;
#else /* FCV_SNIPPET */
	spinlock_t rlock;				//\lnlbl{rlock}
#endif /* FCV_SNIPPET */
	int ridx;					//\lnlbl{ridx}
	/* char pad2[CACHE_LINE_SIZE - sizeof(spinlock_t) - sizeof(int)]; */
	struct deq bkt[PDEQ_N_BKTS];			//\lnlbl{bkt}
};
//\end{snippet}

static int moveleft(int idx)
{
	return (idx - 1) & (PDEQ_N_BKTS - 1);
}

static int moveright(int idx)
{
	return (idx + 1) & (PDEQ_N_BKTS - 1);
}

void init_pdeq(struct pdeq *d)
{
	int i;

	d->lidx = 0;
	spin_lock_init(&d->llock);
	d->ridx = 1;
	spin_lock_init(&d->rlock);
	for (i = 0; i < PDEQ_N_BKTS; i++)
		init_deq(&d->bkt[i]);
}

//\begin{snippet}[labelbase=ln:SMPdesign:lockhdeq:pop_push,commandchars=\\\@\$]
struct cds_list_head *pdeq_pop_l(struct pdeq *d)//\lnlbl{popl:b}
{
	struct cds_list_head *e;
	int i;

	spin_lock(&d->llock);			//\lnlbl{popl:acq}
	i = moveright(d->lidx);			//\lnlbl{popl:idx}
	e = deq_pop_l(&d->bkt[i]);		//\lnlbl{popl:deque}
	if (e != NULL)				//\lnlbl{popl:check}
		d->lidx = i;			//\lnlbl{popl:record}
	spin_unlock(&d->llock);			//\lnlbl{popl:rel}
	return e;				//\lnlbl{popl:return}
}						//\lnlbl{popl:e}

struct cds_list_head *pdeq_pop_r(struct pdeq *d)
{
	struct cds_list_head *e;
	int i;

	spin_lock(&d->rlock);
	i = moveleft(d->ridx);
	e = deq_pop_r(&d->bkt[i]);
	if (e != NULL)
		d->ridx = i;
	spin_unlock(&d->rlock);
	return e;
}

void pdeq_push_l(struct cds_list_head *e, struct pdeq *d)//\lnlbl{pushl:b}
{
	int i;

	spin_lock(&d->llock);				//\lnlbl{pushl:acq}
	i = d->lidx;					//\lnlbl{pushl:idx}
	deq_push_l(e, &d->bkt[i]);			//\lnlbl{pushl:enque}
	d->lidx = moveleft(d->lidx);			//\lnlbl{pushl:update}
	spin_unlock(&d->llock);				//\lnlbl{pushl:rel}
}							//\lnlbl{pushl:e}

void pdeq_push_r(struct cds_list_head *e, struct pdeq *d)
{
	int i;

	spin_lock(&d->rlock);
	i = d->ridx;
	deq_push_r(e, &d->bkt[i]);
	d->ridx = moveright(d->ridx);
	spin_unlock(&d->rlock);
}
//\end{snippet}

#ifdef TEST
#define DEQ_AND_PDEQ
#include "deqtorture.h"
#endif /* #ifdef TEST */
