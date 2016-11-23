/*
 * lockrwdeq.c: simple rw lock-based parallel deq implementation.
 * 	This is similar to lockdeq.c, but expresses the parallel
 * 	implementation in terms of a rw lock with an atomic counter.
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
 * Copyright (c) 2015 Dominik Dingel, IBM Corporation.
 */

#include "../api.h"

/* First do the underlying deq implementation. */

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
 * And now the concurrent implementation, which uses a counter and a rw lock.
 * The counter holds the current available number of items to modify.
 * Before doing a modification we acquire a read lock and reserve our item to modify
 * (link/unlink).
 * If there are not enough items left for true parallel access we will upgrade
 * the read lock, to a write lock, making the access truly sequential.
 */

struct pdeq {
	pthread_rwlock_t lock;
	atomic_t counter;
	struct deq deq_cnt;
};

void init_pdeq(struct pdeq *d)
{
	pthread_rwlock_init(&d->lock, NULL);
	atomic_set(&d->counter, 0);
	init_deq(&d->deq_cnt);
}

struct cds_list_head *pdeq_pop_l(struct pdeq *d)
{
	struct cds_list_head *e;
	pthread_rwlock_rdlock(&d->lock);
	if (atomic_sub_return(2, &d->counter) < 1) {
		pthread_rwlock_unlock(&d->lock);
		pthread_rwlock_wrlock(&d->lock);
	}
	e = deq_pop_l(&d->deq_cnt);
	if (e == NULL)
		atomic_inc(&d->counter);
	atomic_inc(&d->counter);
	pthread_rwlock_unlock(&d->lock);
	return e;
}

struct cds_list_head *pdeq_pop_r(struct pdeq *d)
{
	struct cds_list_head *e;
	pthread_rwlock_rdlock(&d->lock);
	if (atomic_sub_return(2, &d->counter) < 1) {
		pthread_rwlock_unlock(&d->lock);
		pthread_rwlock_wrlock(&d->lock);
	}
	e = deq_pop_r(&d->deq_cnt);
	if (e == NULL)
		atomic_inc(&d->counter);
	atomic_inc(&d->counter);
	pthread_rwlock_unlock(&d->lock);
	return e;
}

void pdeq_push_l(struct cds_list_head *e, struct pdeq *d)
{
	pthread_rwlock_rdlock(&d->lock);
	if (atomic_sub_return(1, &d->counter) < 1) {
		pthread_rwlock_unlock(&d->lock);
		pthread_rwlock_wrlock(&d->lock);
	}
	deq_push_l(e, &d->deq_cnt);
	atomic_add(2, &d->counter);
	pthread_rwlock_unlock(&d->lock);
}

void pdeq_push_r(struct cds_list_head *e, struct pdeq *d)
{
	pthread_rwlock_rdlock(&d->lock);
	if (atomic_sub_return(1, &d->counter) < 1) {
		pthread_rwlock_unlock(&d->lock);
		pthread_rwlock_wrlock(&d->lock);
	}
	deq_push_r(e, &d->deq_cnt);
	atomic_add(2, &d->counter);
	pthread_rwlock_unlock(&d->lock);
}

#ifdef TEST
#include "deqtorture.h"
#endif /* #ifdef TEST */
