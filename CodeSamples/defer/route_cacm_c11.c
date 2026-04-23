/*
 * route_cacm_c11.c: Trivial C11 linked-list routing table protected
 *		by CACM RCU.
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
 * Copyright (c) 2026 Paul E. McKenney, Meta Platforms, Inc.
 */

#ifndef CHECK_C11
#include "../api.h"
#endif // #ifndef CHECK_C11
#include <stdatomic.h>
#include <threads.h>
#include <assert.h>

#ifdef CHECK_C11
#define CACHE_LINE_SIZE 64
#define NR_THREADS 512
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#endif // #ifdef CHECK_C11

#undef rcu_dereference
#undef rcu_assign_pointer

/* Trivial preemptible RCU implementation. */

#define rcu_dereference(p) atomic_load_explicit(&(p), memory_order_acquire)
#define rcu_assign_pointer(p, v) atomic_store_explicit(&(p), v, memory_order_release)

static mtx_t rcu_gp_lock;
static once_flag rcu_gp_lock_flag = ONCE_FLAG_INIT;
static mtx_t routelock;

static void lock_init(void)
{
	mtx_init(&rcu_gp_lock, mtx_plain);
	mtx_init(&routelock, mtx_plain);
}

struct per_thread_rcu {
	_Atomic int rcu_nesting;
	char pad[CACHE_LINE_SIZE - sizeof(int)];
};

int _Thread_local myidx;
_Atomic int nthreads;

struct per_thread_rcu per_thread_rcu[NR_THREADS];

static void rcu_read_lock(void)
{
	int nesting;
	_Atomic int *rnp = &per_thread_rcu[myidx].rcu_nesting;

	nesting = atomic_load_explicit(rnp, memory_order_relaxed);
	atomic_store_explicit(rnp, nesting + 1, memory_order_relaxed);
	atomic_thread_fence(memory_order_seq_cst); // Can be optimized away
}

static void rcu_read_unlock(void)
{
	int nesting;
	_Atomic int *rnp = &per_thread_rcu[myidx].rcu_nesting;

	atomic_thread_fence(memory_order_seq_cst); // Can be optimized away
	nesting = atomic_load_explicit(rnp, memory_order_relaxed);
	atomic_store_explicit(rnp, nesting - 1, memory_order_relaxed);
}

void synchronize_rcu(void)
{
	int i;
	struct per_thread_rcu *ptrp;

	atomic_thread_fence(memory_order_seq_cst);
	call_once(&rcu_gp_lock_flag, lock_init);
	mtx_lock(&rcu_gp_lock);
	for (i = 0; i < NR_THREADS; i++) {
		ptrp = &per_thread_rcu[i];
		while (atomic_load_explicit(&ptrp->rcu_nesting, memory_order_relaxed))
			continue;
	}
	mtx_unlock(&rcu_gp_lock);
	atomic_thread_fence(memory_order_seq_cst);
}

void route_register_thread(void)
{
	myidx = atomic_fetch_add(&nthreads, 1);
}

void route_unregister_thread(void)
{
	atomic_thread_fence(memory_order_seq_cst);
	assert(atomic_load(&per_thread_rcu[myidx].rcu_nesting) == 0);
}

#define route_register_thread route_register_thread
#define route_unregister_thread route_unregister_thread
#define quiescent_state() do { } while (0)

/* Route-table entry to be included in the routing list. */
struct route_entry {
	struct route_entry *volatile _Atomic next;
	unsigned long addr;
	unsigned long iface;
	_Atomic int freed;
};

struct route_entry *volatile _Atomic route_list;
static mtx_t routelock;

static void re_free(struct route_entry *rep)
{
	atomic_store_explicit(&rep->freed, 1, memory_order_relaxed);
	free(rep);
}

/*
 * Look up a route entry, return the corresponding interface.
 */
unsigned long route_lookup(unsigned long addr)
{
	struct route_entry *rep;
	unsigned long ret;

	rcu_read_lock();
	for (rep = rcu_dereference(route_list); rep;
	     rep = rcu_dereference(rep->next)) {
		if (rep->addr == addr) {
			ret = rep->iface;
			if (atomic_load_explicit(&rep->freed, memory_order_relaxed))
				abort();
			rcu_read_unlock();
			return ret;
		}
	}
	rcu_read_unlock();
	return ULONG_MAX;
}

/*
 * Add an element to the route table.
 */
int route_add(unsigned long addr, unsigned long interface)
{
	struct route_entry *rep;

	rep = malloc(sizeof(*rep));
	if (!rep)
		return -ENOMEM;
	rep->addr = addr;
	rep->iface = interface;
	atomic_store_explicit(&rep->freed, 0, memory_order_relaxed);
	call_once(&rcu_gp_lock_flag, lock_init);
	mtx_lock(&routelock);
	atomic_store_explicit(&rep->next, rcu_dereference(route_list),
			      memory_order_relaxed);
	rcu_assign_pointer(route_list, rep);
	mtx_unlock(&routelock);
	return 0;
}

/*
 * Remove the specified element from the route table.
 */
int route_del(unsigned long addr)
{
	struct route_entry *rep;
	struct route_entry *volatile _Atomic *repp;

	call_once(&rcu_gp_lock_flag, lock_init);
	mtx_lock(&routelock);
	for (repp = &route_list; *repp;
	     rep = rcu_dereference(*repp), repp = &rep->next) {
		rep = rcu_dereference(*repp);
		if (rep->addr == addr) {
			rcu_assign_pointer(*repp, rep->next);
			mtx_unlock(&routelock);
			synchronize_rcu();
			re_free(rep);
			return 0;
		}
	}
	mtx_unlock(&routelock);
	return -ENOENT;
}

/*
 * Clear all elements from the route table.
 */
void route_clear(void)
{
	struct route_entry *rep;
	struct route_entry *rep_local;

	call_once(&rcu_gp_lock_flag, lock_init);
	mtx_lock(&routelock);
	rep_local = rcu_dereference(route_list);
	rcu_assign_pointer(route_list, NULL);
	synchronize_rcu();
	for (rep = rep_local; rep; rep = rep_local) {
		if (!rep)
			return;
		rep_local = rcu_dereference(rep->next);
		re_free(rep);
	}
}


#ifndef CHECK_C11
#include "routetorture.h"
#endif // #ifndef CHECK_C11
