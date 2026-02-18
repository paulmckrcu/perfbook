/*
 * route_cacm.c: Trivial linked-list routing table protected by CACM RCU.
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

#define _GNU_SOURCE
#define _LGPL_SOURCE

#ifndef DO_QSBR
#define RCU_SIGNAL
#include <urcu.h>
#else /* #ifndef DO_QSBR */
#include <urcu-qsbr.h>
#endif /* #else #ifndef DO_QSBR */

#include "../api.h"

/* Route-table entry to be included in the routing list. */
struct route_entry {
	struct route_entry *next;
	unsigned long addr;
	unsigned long iface;
	int freed;
};

struct route_entry *route_list;
DEFINE_SPINLOCK(routelock);

static void re_free(struct route_entry *rep)
{
	WRITE_ONCE(rep->freed, 1);
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
			if (READ_ONCE(rep->freed))
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
	rep->freed = 0;
	spin_lock(&routelock);
	rep->next = route_list;
	route_list = rep;
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
	for (repp = &route_list; *repp;
	     rep = rcu_dereference(*repp), repp = &rep->next) {
		rep = rcu_dereference(*repp);
		if (rep->addr == addr) {
			rcu_assign_pointer(*repp, rep->next);
			spin_unlock(&routelock);
			synchronize_rcu();
			re_free(rep);
			return 0;
		}
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
	struct route_entry *rep_local;

	spin_lock(&routelock);
	rep_local = route_list;
	route_list = NULL;
	synchronize_rcu();
	for (rep = rep_local; rep; rep = rep_local) {
		if (!rep)
			return;
		rep_local = rep->next;
		re_free(rep);
	}
}


#define route_register_thread() rcu_register_thread()
#define route_unregister_thread() rcu_unregister_thread()

#define quiescent_state() rcu_quiescent_state()

#include "routetorture.h"
