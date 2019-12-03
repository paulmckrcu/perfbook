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
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

/* First do the underlying single-locked deq implementation. */

struct deq {
	struct cds_list_head chain;
} ____cacheline_internodealigned_in_smp;

void init_deq(struct deq *p)
{
	CDS_INIT_LIST_HEAD(&p->chain);
}

struct cds_list_head *deq_pop_l(struct deq *p)
{
	struct cds_list_head *e;

	if (cds_list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.prev;
		cds_list_del(e);
		CDS_INIT_LIST_HEAD(e);
	}
	return e;
}

void deq_push_l(struct cds_list_head *e, struct deq *p)
{
	cds_list_add_tail(e, &p->chain);
}

struct cds_list_head *deq_pop_r(struct deq *p)
{
	struct cds_list_head *e;

	if (cds_list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.next;
		cds_list_del(e);
		CDS_INIT_LIST_HEAD(e);
	}
	return e;
}

void deq_push_r(struct cds_list_head *e, struct deq *p)
{
	cds_list_add(e, &p->chain);
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

//\begin{snippet}[labelbase=ln:SMPdesign:locktdeq:pop_push,commandchars=\\\@\$]
struct cds_list_head *pdeq_pop_l(struct pdeq *d)		//\lnlbl{popl:b}
{
	struct cds_list_head *e;

	spin_lock(&d->llock);					//\lnlbl{popl:acq:l}
	e = deq_pop_l(&d->ldeq);				//\lnlbl{popl:deq:ll}
	if (e == NULL) {
		spin_lock(&d->rlock);				//\lnlbl{popl:acq:r}
		e = deq_pop_l(&d->rdeq);			//\lnlbl{popl:deq:lr}
		cds_list_splice(&d->rdeq.chain, &d->ldeq.chain);//\lnlbl{popl:move}
		CDS_INIT_LIST_HEAD(&d->rdeq.chain);		//\lnlbl{popl:init:r}
		spin_unlock(&d->rlock);				//\lnlbl{popl:rel:r}
	}							//\lnlbl{popl:skip}
	spin_unlock(&d->llock);					//\lnlbl{popl:rel:l}
	return e;
}								//\lnlbl{popl:e}

struct cds_list_head *pdeq_pop_r(struct pdeq *d)		//\lnlbl{popr:b}
{
	struct cds_list_head *e;

	spin_lock(&d->rlock);					//\lnlbl{popr:acq:r1}
	e = deq_pop_r(&d->rdeq);				//\lnlbl{popr:deq:rr1}
	if (e == NULL) {					//\lnlbl{popr:check1}
		spin_unlock(&d->rlock);				//\lnlbl{popr:rel:r1}
		spin_lock(&d->llock);				//\lnlbl{popr:acq:l}
		spin_lock(&d->rlock);				//\lnlbl{popr:acq:r2}
		e = deq_pop_r(&d->rdeq);			//\lnlbl{popr:deq:rr2}
		if (e == NULL) {				//\lnlbl{popr:check2}
			e = deq_pop_r(&d->ldeq);			//\lnlbl{popr:deq:rl}
			cds_list_splice(&d->ldeq.chain, &d->rdeq.chain);//\lnlbl{popr:move}
			CDS_INIT_LIST_HEAD(&d->ldeq.chain);		//\lnlbl{popr:init:l}
		}
		spin_unlock(&d->llock);				//\lnlbl{popr:rel:l}
	}							//\lnlbl{popr:skip2}
	spin_unlock(&d->rlock);					//\lnlbl{popr:rel:r2}
	return e;
}								//\lnlbl{popr:e}

void pdeq_push_l(struct cds_list_head *e, struct pdeq *d)	//\lnlbl{pushl:b}
{
	spin_lock(&d->llock);					//\lnlbl{pushl:acq:l}
	deq_push_l(e, &d->ldeq);				//\lnlbl{pushl:que:l}
	spin_unlock(&d->llock);					//\lnlbl{pushl:rel:l}
}								//\lnlbl{pushl:e}

void pdeq_push_r(struct cds_list_head *e, struct pdeq *d)	//\lnlbl{pushr:b}
{
	spin_lock(&d->rlock);
	deq_push_r(e, &d->rdeq);
	spin_unlock(&d->rlock);
}								//\lnlbl{pushr:e}
//\end{snippet}

#ifdef TEST
#include "deqtorture.h"
#endif /* #ifdef TEST */
