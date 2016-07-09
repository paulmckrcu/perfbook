/*
 * route_hazptr.c: Trivial linked-list routing table protected by hazard
 *	pointers.
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

#include "../api.h"
#include "hazptr.h"

/* Route-table entry to be included in the routing list. */
struct route_entry {
	struct hazptr_head hh;
	struct route_entry *re_next;
	unsigned long addr;
	unsigned long iface;
	int re_freed;
};

struct route_entry route_list;
DEFINE_SPINLOCK(routelock);

/* This thread's fixed-sized set of hazard pointers. */
hazard_pointer __thread *my_hazptr;

/*
 * Look up a route entry, return the corresponding interface. 
 */
unsigned long route_lookup(unsigned long addr)
{
	int offset = 0;
	struct route_entry *rep;
	struct route_entry **repp;

retry:
	repp = &route_list.re_next;
	do {
		rep = ACCESS_ONCE(*repp);
		if (rep == NULL)
			return ULONG_MAX;
		if (rep == (struct route_entry *)HAZPTR_POISON)
			goto retry; /* element deleted. */

		/* Store a hazard pointer. */
		my_hazptr[offset].p = &rep->hh;
		offset = !offset;
		smp_mb(); /* Force pointer loads in order. */

		/* Recheck the hazard pointer against the original. */
		if (ACCESS_ONCE(*repp) != rep)
			goto retry;

		/* Advance to next. */
		repp = &rep->re_next;
	} while (rep->addr != addr);
	if (ACCESS_ONCE(rep->re_freed))
		abort();
	return rep->iface;
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
	rep->re_freed = 0;
	spin_lock(&routelock);
	rep->re_next = route_list.re_next;
	route_list.re_next = rep;
	spin_unlock(&routelock);
	return 0;
}

/*
 * Remove the specified element from the route table.
 */
int route_del(unsigned long addr)
{
	struct route_entry *rep;
	struct route_entry **repp;

	spin_lock(&routelock);
	repp = &route_list.re_next;
	for (;;) {
		rep = *repp;
		if (rep == NULL)
			break;
		if (rep->addr == addr) {
			*repp = rep->re_next;
			rep->re_next = (struct route_entry *)HAZPTR_POISON;
			spin_unlock(&routelock);
			hazptr_free_later(&rep->hh);
			return 0;
		}
		repp = &rep->re_next;
	}
	spin_unlock(&routelock);
	return -ENOENT;
}

/*
 * Clear all elements from the route table.
 */
void route_clear(void)
{
	struct route_entry *rep;
	struct route_entry *rep1;

	spin_lock(&routelock);
	rep = route_list.re_next;
	ACCESS_ONCE(route_list.re_next) = NULL;
	while (rep != NULL) {
		rep1 = rep->re_next;
		rep->re_next = (struct route_entry *)HAZPTR_POISON;
		hazptr_free_later(&rep->hh);
		rep = rep1;
	}
	spin_unlock(&routelock);
}

void route_register_thread(void)
{
	my_hazptr = &HP[K * smp_thread_id()];
}
#define route_register_thread route_register_thread

#define route_unregister_thread() hazptr_thread_exit()

#define quiescent_state() do { } while (0)

#define synchronize_rcu() do { } while (0)

#define other_init() hazptr_init()

void hazptr_free(void *p)
{
	struct route_entry *rep = p;

	ACCESS_ONCE(rep->re_freed) = 1;
	free(p);
}

#include "routetorture.h"
