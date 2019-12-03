/*
 * route_refcnt.c: Trivial linked-list routing table protected by reference
 *	counts, but not protected very well.  To reiterate: BUGGY!!!
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

#include "../api.h"

/* Route-table entry to be included in the routing list. */
//\begin{snippet}[labelbase=ln:defer:route_refcnt:lookup,commandchars=\\\[\]]
struct route_entry {
	atomic_t re_refcnt;				//\lnlbl{entry:refcnt}
	struct route_entry *re_next;
	unsigned long addr;
	unsigned long iface;
	int re_freed;					//\lnlbl{entry:freed}
};
							//\fcvexclude
struct route_entry route_list;
DEFINE_SPINLOCK(routelock);				//\lnlbl{entry:routelock}

static void re_free(struct route_entry *rep)		//\lnlbl{re_free:b}
{
	WRITE_ONCE(rep->re_freed, 1);
	free(rep);
}							//\lnlbl{re_free:e}

/*
 * Look up a route entry, return the corresponding interface.
 */
unsigned long route_lookup(unsigned long addr)
{
	int old;
	int new;
	struct route_entry *rep;
	struct route_entry **repp;
	unsigned long ret;

retry:
	repp = &route_list.re_next;
	rep = NULL;
	do {
		if (rep && atomic_dec_and_test(&rep->re_refcnt)) //\lnlbl{lookup:relprev:b}
			re_free(rep);				//\lnlbl{lookup:relprev:e}
		rep = READ_ONCE(*repp);
		if (rep == NULL)				//\lnlbl{lookup:check_NULL}
			return ULONG_MAX;
								//\fcvexclude
		/* Acquire a reference if the count is non-zero. */
		do {						//\lnlbl{lookup:acq:b}
			if (READ_ONCE(rep->re_freed))		//\lnlbl{lookup:check_uaf}
				abort();			//\lnlbl{lookup:abort}
			old = atomic_read(&rep->re_refcnt);
			if (old <= 0)
				goto retry;
			new = old + 1;
		} while (atomic_cmpxchg(&rep->re_refcnt,
		                        old, new) != old);	//\lnlbl{lookup:acq:e}
								//\fcvexclude
		/* Advance to next. */
		repp = &rep->re_next;
	} while (rep->addr != addr);
	ret = rep->iface;
	if (atomic_dec_and_test(&rep->re_refcnt))
		re_free(rep);
	return ret;
}
//\end{snippet}

/*
 * Add an element to the route table.
 */
//\begin{snippet}[labelbase=ln:defer:route_refcnt:add_del,commandchars=\\\[\]]
int route_add(unsigned long addr, unsigned long interface)
{
	struct route_entry *rep;

	rep = malloc(sizeof(*rep));
	if (!rep)
		return -ENOMEM;
	atomic_set(&rep->re_refcnt, 1);
	rep->addr = addr;
	rep->iface = interface;
	spin_lock(&routelock);				//\lnlbl{acq1}
	rep->re_next = route_list.re_next;
	rep->re_freed = 0;				//\lnlbl{init:freed}
	route_list.re_next = rep;
	spin_unlock(&routelock);			//\lnlbl{rel1}
	return 0;
}

/*
 * Remove the specified element from the route table.
 */
int route_del(unsigned long addr)
{
	struct route_entry *rep;
	struct route_entry **repp;

	spin_lock(&routelock);				//\lnlbl{acq2}
	repp = &route_list.re_next;
	for (;;) {
		rep = *repp;
		if (rep == NULL)
			break;
		if (rep->addr == addr) {
			*repp = rep->re_next;
			spin_unlock(&routelock);	//\lnlbl{rel2}
			if (atomic_dec_and_test(&rep->re_refcnt)) //\lnlbl{re_free:b}
				re_free(rep);		//\lnlbl{re_free:e}
			return 0;
		}
		repp = &rep->re_next;
	}
	spin_unlock(&routelock);			//\lnlbl{rel3}
	return -ENOENT;
}
//\end{snippet}

/*
 * Clear all elements from the route table.
 */
void route_clear(void)
{
	struct route_entry *rep;
	struct route_entry *rep1;

	spin_lock(&routelock);
	rep = route_list.re_next;
	WRITE_ONCE(route_list.re_next, NULL);
	while (rep != NULL) {
		rep1 = rep->re_next;
		if (atomic_dec_and_test(&rep->re_refcnt))
			re_free(rep);
		rep = rep1;
	}
	spin_unlock(&routelock);
}

#define quiescent_state() rcu_quiescent_state()

#define route_register_thread() do { } while (0)
#define route_unregister_thread() do { } while (0)

#define synchronize_rcu() do { } while (0)

#include "routetorture.h"
