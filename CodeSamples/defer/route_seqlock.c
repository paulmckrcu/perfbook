/*
 * route_seqlock.c: Trivial linked-list routing table "protected" by
 *	sequence locking.  To reiterate: BUGGY!!!
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
#include "seqlock.h"

/* Route-table entry to be included in the routing list. */
struct route_entry {
	struct route_entry *re_next;
	unsigned long addr;
	unsigned long iface;
};

struct route_entry route_list;
DEFINE_SPINLOCK(routelock);
DEFINE_SEQ_LOCK(sl);

/*
 * Look up a route entry, return the corresponding interface. 
 */
unsigned long route_lookup(unsigned long addr)
{
	struct route_entry *rep;
	struct route_entry **repp;
	unsigned long ret;
	unsigned long s;

retry:
	s = read_seqbegin(&sl);
	repp = &route_list.re_next;
	do {
		rep = ACCESS_ONCE(*repp);
		if (rep == NULL) {
			if (read_seqretry(&sl, s))
				goto retry;
			return ULONG_MAX;
		}

		/* Advance to next. */
		repp = &rep->re_next;
	} while (rep->addr != addr);
	ret = rep->iface;
	if (read_seqretry(&sl, s))
		goto retry;
	return ret;
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
	write_seqlock(&sl);
	rep->re_next = route_list.re_next;
	route_list.re_next = rep;
	write_sequnlock(&sl);
	return 0;
}

/*
 * Remove the specified element from the route table.
 */
int route_del(unsigned long addr)
{
	struct route_entry *rep;
	struct route_entry **repp;

	write_seqlock(&sl);
	repp = &route_list.re_next;
	for (;;) {
		rep = *repp;
		if (rep == NULL)
			break;
		if (rep->addr == addr) {
			*repp = rep->re_next;
			write_sequnlock(&sl);
			/* Poison pointer for debugging purposes. */
			rep->re_next = (struct route_entry *)1UL;
			free(rep);
			return 0;
		}
		repp = &rep->re_next;
	}
	write_sequnlock(&sl);
	return -ENOENT;
}

/*
 * Clear all elements from the route table.
 */
void route_clear(void)
{
	struct route_entry *rep;
	struct route_entry *rep1;

	write_seqlock(&sl);
	rep = route_list.re_next;
	ACCESS_ONCE(route_list.re_next) = NULL;
	while (rep != NULL) {
		rep1 = rep->re_next;
		free(rep);
		rep = rep1;
	}
	write_sequnlock(&sl);
}

#define quiescent_state() rcu_quiescent_state()

#define route_register_thread() do { } while (0)
#define route_unregister_thread() do { } while (0)

#define synchronize_rcu() do { } while (0)

#include "routetorture.h"
