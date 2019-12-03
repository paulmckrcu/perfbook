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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include "hazptr.h"

/* Route-table entry to be included in the routing list. */
//\begin{snippet}[labelbase=ln:defer:route_hazptr:lookup,commandchars=\\\@\$]
struct route_entry {
	struct hazptr_head hh;				//\lnlbl{hh}
	struct route_entry *re_next;
	unsigned long addr;
	unsigned long iface;
	int re_freed;					//\lnlbl{re_freed}
};
								//\fcvexclude
struct route_entry route_list;
DEFINE_SPINLOCK(routelock);
								//\fcvexclude
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

retry:							//\lnlbl{retry}
	repp = &route_list.re_next;
	do {
		rep = hp_try_record(repp, &my_hazptr[offset]);	//\lnlbl{tryrecord}
		if (!rep)
			return ULONG_MAX;			//\lnlbl{NULL}
		if ((uintptr_t)rep == HAZPTR_POISON)
			goto retry; /* element deleted. */	//\lnlbl{deleted}
		repp = &rep->re_next;
	} while (rep->addr != addr);
	if (READ_ONCE(rep->re_freed))
		abort();					//\lnlbl{abort}
	return rep->iface;
}
//\end{snippet}

/*
 * Add an element to the route table.
 */
//\begin{snippet}[labelbase=ln:defer:route_hazptr:add_del,commandchars=\\\[\]]
int route_add(unsigned long addr, unsigned long interface)
{
	struct route_entry *rep;

	rep = malloc(sizeof(*rep));
	if (!rep)
		return -ENOMEM;
	rep->addr = addr;
	rep->iface = interface;
	rep->re_freed = 0;				//\lnlbl{init_freed}
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
			rep->re_next = (struct route_entry *)HAZPTR_POISON; //\lnlbl{poison}
			spin_unlock(&routelock);
			hazptr_free_later(&rep->hh);	//\lnlbl{free_later}
			return 0;
		}
		repp = &rep->re_next;
	}
	spin_unlock(&routelock);
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

	WRITE_ONCE(rep->re_freed, 1);
	free(p);
}

#include "routetorture.h"
