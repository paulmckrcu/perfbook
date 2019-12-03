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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
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
//\begin{snippet}[labelbase=ln:defer:route_rcu:lookup,commandchars=\\\[\]]
struct route_entry {
	struct rcu_head rh;			//\lnlbl{rh}
	struct cds_list_head re_next;
	unsigned long addr;
	unsigned long iface;
	int re_freed;				//\lnlbl{re_freed}
};
								//\fcvexclude
CDS_LIST_HEAD(route_list);
DEFINE_SPINLOCK(routelock);
#ifndef FCV_SNIPPET
static void re_free(struct route_entry *rep)
{
	WRITE_ONCE(rep->re_freed, 1);
	free(rep);
}
#endif /* FCV_SNIPPET */

/*
 * Look up a route entry, return the corresponding interface.
 */
unsigned long route_lookup(unsigned long addr)
{
	struct route_entry *rep;
	unsigned long ret;

	rcu_read_lock();				//\lnlbl{lock}
	cds_list_for_each_entry_rcu(rep, &route_list, re_next) {
		if (rep->addr == addr) {
			ret = rep->iface;
			if (READ_ONCE(rep->re_freed))	//\lnlbl{chk_freed}
				abort();		//\lnlbl{abort}
			rcu_read_unlock();		//\lnlbl{unlock1}
			return ret;
		}
	}
	rcu_read_unlock();				//\lnlbl{unlock2}
	return ULONG_MAX;
}
//\end{snippet}

/*
 * Add an element to the route table.
 */
//\begin{snippet}[labelbase=ln:defer:route_rcu:add_del,commandchars=\\\[\]]
int route_add(unsigned long addr, unsigned long interface)
{
	struct route_entry *rep;

	rep = malloc(sizeof(*rep));
	if (!rep)
		return -ENOMEM;
	rep->addr = addr;
	rep->iface = interface;
	rep->re_freed = 0;
	spin_lock(&routelock);				//\lnlbl{add:lock}
	cds_list_add_rcu(&rep->re_next, &route_list);	//\lnlbl{add:add_rcu}
	spin_unlock(&routelock);			//\lnlbl{add:unlock}
	return 0;
}

static void route_cb(struct rcu_head *rhp)		//\lnlbl{cb:b}
{
#ifndef FCV_SNIPPET
	struct route_entry *rep = container_of(rhp, struct route_entry, rh);

	re_free(rep);
#else /* FCV_SNIPPET */
	struct route_entry *rep;

	rep = container_of(rhp, struct route_entry, rh);
	WRITE_ONCE(rep->re_freed, 1);
	free(rep);
#endif /* FCV_SNIPPET */
}							//\lnlbl{cb:e}

/*
 * Remove the specified element from the route table.
 */
int route_del(unsigned long addr)
{
	struct route_entry *rep;

	spin_lock(&routelock);				//\lnlbl{del:lock}
	cds_list_for_each_entry(rep, &route_list, re_next) {
		if (rep->addr == addr) {
			cds_list_del_rcu(&rep->re_next);//\lnlbl{del:del_rcu}
			spin_unlock(&routelock);	//\lnlbl{del:unlock1}
			call_rcu(&rep->rh, route_cb);	//\lnlbl{del:call_rcu}
			return 0;
		}
	}
	spin_unlock(&routelock);			//\lnlbl{del:unlock2}
	return -ENOENT;
}
//\end{snippet}

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
