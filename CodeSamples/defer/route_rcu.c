/*
 * route_rcu.c: Trivial linked-list routing table protected by RCU.
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

#define _GNU_SOURCE
#define _LGPL_SOURCE

// Uncomment to enable signal-based RCU.  (Need corresponding Makefile change!)
#define RCU_SIGNAL
#include <urcu.h>

// Uncomment to enable QSBR.  (Need corresponding Makefile change!)
//#include <urcu-qsbr.h>

#include "../api.h"

/* Route-table entry to be included in the routing list. */
struct route_entry {
	struct rcu_head rh;
	struct cds_list_head re_next;
	unsigned long addr;
	unsigned long iface;
	int re_freed;
};

CDS_LIST_HEAD(route_list);
DEFINE_SPINLOCK(routelock);

static void re_free(struct route_entry *rep)
{
	ACCESS_ONCE(rep->re_freed) = 1;
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
	cds_list_for_each_entry_rcu(rep, &route_list, re_next) {
		if (rep->addr == addr) {
			ret = rep->iface;
			if (ACCESS_ONCE(rep->re_freed))
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
	rep->re_freed = 0;
	spin_lock(&routelock);
	cds_list_add_rcu(&rep->re_next, &route_list);
	spin_unlock(&routelock);
	return 0;
}

static void route_cb(struct rcu_head *rhp)
{
	struct route_entry *rep = container_of(rhp, struct route_entry, rh);

	ACCESS_ONCE(rep->re_freed) = 1;
	re_free(rep);
}

/*
 * Remove the specified element from the route table.
 */
int route_del(unsigned long addr)
{
	struct route_entry *rep;

	spin_lock(&routelock);
	cds_list_for_each_entry(rep, &route_list, re_next) {
		if (rep->addr == addr) {
			cds_list_del_rcu(&rep->re_next);
			spin_unlock(&routelock);
			call_rcu(&rep->rh, route_cb);
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
	struct cds_list_head junk;
	struct route_entry *rep;
	struct route_entry *rep1;

	CDS_INIT_LIST_HEAD(&junk);
	spin_lock(&routelock);
	cds_list_for_each_entry_safe(rep, rep1, &route_list, re_next) {
		cds_list_del_rcu(&rep->re_next);
		cds_list_add_rcu(&rep->re_next, &junk);
	}
	spin_unlock(&routelock);
	synchronize_rcu();
	cds_list_for_each_entry_safe(rep, rep1, &junk, re_next)
		re_free(rep);
}


#define route_register_thread() rcu_register_thread()
#define route_unregister_thread() rcu_unregister_thread()

#define quiescent_state() rcu_quiescent_state()

#include "routetorture.h"
