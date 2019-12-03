/*
 * existence.c: Manage existence data structures.
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
 * Copyright (c) 2014-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include <stdlib.h>
#ifdef USE_JEMALLOC
#include <jemalloc/jemalloc.h>
#endif /* #ifdef USE_JEMALLOC */
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "../../api.h"
#include "existence.h"
#define _GNU_SOURCE
#define _LGPL_SOURCE
#define RCU_SIGNAL
#include <urcu.h>

/* Existence-switch array. */
const int existence_array[4] = { 1, 0, 0, 1 };

/* Existence structure associated with each moving structure. */
struct existence {
	const int **existence_switch;
	int offset;
};

/* Existence-group structure associated with multi-structure change. */
struct existence_group {
	struct existence outgoing;
	struct existence incoming;
	const int *existence_switch;
	struct rcu_head rh;
	struct existence_group *next;
};

/*
 * Existence-group per-thread cache structure, which can be wired up to
 * dump excess free blocks to another such cache.  Multilevel linkages
 * are not allowed.
 */
struct existence_group_cache {
	struct existence_group *free;
	struct existence_group **tail;
	long nfree;
	struct existence_group_cache *egcp;
	spinlock_t lock __attribute__((__aligned__(CACHE_LINE_SIZE)));
	struct existence_group *ffree;
	struct existence_group **ftail;
	long nffree;
	struct rcu_head rh;
};

#define EXISTENCE_MALLOC_BATCH 32768
#define EXISTENCE_MALLOC_CACHE (2 * EXISTENCE_MALLOC_BATCH)

struct existence_group_cache __thread egp_cache;

static void existence_alloc_cache_init(void)
{
	spin_lock_init(&egp_cache.lock);
	egp_cache.egcp = NULL;
	egp_cache.free = NULL;
	egp_cache.tail = &egp_cache.free;
	egp_cache.nfree = 0;
	egp_cache.ffree = NULL;
	egp_cache.ftail = &egp_cache.ffree;
	egp_cache.nffree = 0;
}

static void existence_free_cache(struct existence_group *egp)
{
#ifdef BAD_MALLOC
	struct existence_group_cache *egcop;

	if (!egp_cache.tail)
		existence_alloc_cache_init();
	egcop = egp_cache.egcp;
	if (egp_cache.nfree > EXISTENCE_MALLOC_CACHE && egcop) {
		spin_lock(&egcop->lock);
		*(egcop->ftail) = egp_cache.free;
		egcop->ftail = egp_cache.tail;
		egcop->nffree += egp_cache.nfree;
		egp_cache.free = NULL;
		egp_cache.tail = &egp_cache.free;
		egp_cache.nfree = 0;
		spin_unlock(&egcop->lock);
	}
	egp->next = NULL;
	*egp_cache.tail = egp;
	egp_cache.tail = &egp->next;
	egp_cache.nfree++;
#else /* #ifdef BAD_MALLOC */
	free(egp);
#endif /* #else #ifdef BAD_MALLOC */
}

struct existence_group_alloc {
	struct existence_group eg;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

static struct existence_group *existence_alloc_cache(void)
{
#ifdef BAD_MALLOC
	int i;
	struct existence_group *egp;
	struct existence_group_alloc *p;

	if (!egp_cache.tail)
		existence_alloc_cache_init();
	if (!egp_cache.free && ACCESS_ONCE(egp_cache.nffree)) {
		spin_lock(&egp_cache.lock);
		egp_cache.free = egp_cache.ffree;
		egp_cache.tail = egp_cache.ftail;
		egp_cache.nfree = egp_cache.nffree;
		egp_cache.ffree = NULL;
		egp_cache.ftail = &egp_cache.ffree;
		egp_cache.nffree = 0;
		spin_unlock(&egp_cache.lock);
	}
	if (egp_cache.free) {
		egp = egp_cache.free;
		egp_cache.free = egp->next;
		if (!egp_cache.free)
			egp_cache.tail = &egp_cache.free;
		egp_cache.nfree--;
		return egp;
	}
	p = malloc(sizeof(*p) * EXISTENCE_MALLOC_BATCH);
	BUG_ON(!p);
	for (i = EXISTENCE_MALLOC_BATCH - 1; i > 0; i--)
		existence_free_cache(&p[i].eg);
	return &p->eg;
#else /* #ifdef BAD_MALLOC */
	return malloc(sizeof(struct existence_group));
#endif /* #else #ifdef BAD_MALLOC */
}

static void existence_wire_call_rcu_cb(struct rcu_head *rhp)
{
	struct existence_group_cache *egcwp;

	if (!egp_cache.tail)
		existence_alloc_cache_init();
	egcwp = container_of(rhp, struct existence_group_cache, rh);
	egp_cache.egcp = egcwp;
}

/*
 * Wire up this thread's call_rcu() thread's existence_group_cache
 * structure to this thread's structure.  Excess free existence_group
 * structures will henceforth be forwarded to the current thread.
 */
void existence_wire_call_rcu(void)
{
	if (!egp_cache.tail)
		existence_alloc_cache_init();
	call_rcu(&egp_cache.rh, existence_wire_call_rcu_cb);
}

/*
 * Allocate an existence-change group.
 */
struct existence_group *existence_alloc(void)
{
	struct existence_group *egp = existence_alloc_cache();

	if (egp == NULL)
		return NULL;

	egp->outgoing.existence_switch = &egp->existence_switch;
	egp->outgoing.offset = 0;
	egp->incoming.existence_switch = &egp->existence_switch;
	egp->incoming.offset = 1;
	egp->existence_switch = &existence_array[0];
	return egp;
}

/*
 * RCU callback function for freeing existence-change group structure.
 */
static void existence_free_rcu(struct rcu_head *rhp)
{
	struct existence_group *egp =
			container_of(rhp, struct existence_group, rh);

	existence_free_cache(egp);
}

/*
 * Free an existence-change structure via RCU.
 */
void existence_free(struct existence_group *egp)
{
	call_rcu(&egp->rh, existence_free_rcu);
}

/*
 * Switch existence, which atomically deletes all outgoing data elements
 * and inserts all incoming data elements.
 */
void existence_switch(struct existence_group *egp)
{
	smp_mb();
	ACCESS_ONCE(egp->existence_switch) = &existence_array[2];
	smp_mb();
}

/*
 * Does the referenced existence pointer belong to something that
 * currently exists?  Returns zero if yes, -ENOENT otherwise.
 */
int _existence_exists(struct existence *ep)
{
	const int *asp;
	int offset;

	offset = ep->offset;
	asp = smp_load_acquire(ep->existence_switch);
	return asp[offset];
}

/*
 * Does the referenced existence pointer belong to something that
 * currently exists?  Returns zero if yes, -ENOENT otherwise.
 * Relaxed version, no memory-ordering guarantees beyond those needed
 * to avoid garbage.
 */
int _existence_exists_relaxed(struct existence *ep)
{
	const int *asp;
	int offset;

	offset = ep->offset;
	asp = ACCESS_ONCE(*(ep->existence_switch));
	return asp[offset];
}

/*
 * Return the value of the specified existence pointer, with ordering.
 */
struct existence *existence_get(struct existence **epp)
{
	return smp_load_acquire(epp);
}

/*
 * Return the value of the specified existence pointer, without ordering.
 */
struct existence *existence_get_relaxed(struct existence **epp)
{
	return rcu_dereference(*epp);
}

/*
 * Return the outgoing existence structure from the specified
 * existence_group structure.
 */
struct existence *existence_get_outgoing(struct existence_group *egp)
{
	return &egp->outgoing;
}

/*
 * Return the incoming existence structure from the specified
 * existence_group structure.
 */
struct existence *existence_get_incoming(struct existence_group *egp)
{
	return &egp->incoming;
}

/*
 * Set the referenced existence pointer to the specified value.
 */
void existence_set(struct existence **epp, struct existence *ep)
{
	BUG_ON(*epp != NULL);
	smp_store_release(epp, ep);
}

/*
 * Reset the specified existence pointer to permanent.
 */
void existence_clear(struct existence **epp)
{
	BUG_ON(*epp == NULL);
	smp_store_release(epp, NULL);
}

/*
 * Is the referenced existence pointer involved in an outgoing
 * existence-change operation?
 */
int existence_is_outgoing(struct existence **epp)
{
	struct existence *ep = smp_load_acquire(epp);

	if (ep == NULL)
		return 0;
	return ep->offset == 0;
}

/*
 * Is the referenced existence pointer involved in an incoming
 * existence-change operation?
 */
int existence_is_incoming(struct existence **epp)
{
	struct existence *ep = smp_load_acquire(epp);

	if (ep == NULL)
		return 0;
	return ep->offset != 0;
}
