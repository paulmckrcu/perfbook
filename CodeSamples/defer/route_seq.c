/*
 * route_seq.c: Trivial linked-list routing table protected by nothing,
 *	thus allowing multiple readers with no updater or single updater.
 *	Running --stresstest with this version will result in failures.
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

/* Route-table entry to be included in the routing list. */
struct route_entry {
	struct cds_list_head re_next;
	unsigned long re_addr;
	unsigned long re_interface;
};

CDS_LIST_HEAD(route_list);

/*
 * Look up a route entry, return the corresponding interface. 
 */
unsigned long route_lookup(unsigned long addr)
{
	struct route_entry *rep;
	unsigned long ret;

	cds_list_for_each_entry(rep, &route_list, re_next) {
		if (rep->re_addr == addr) {
			ret = rep->re_interface;
			return ret;
		}
	}
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
	rep->re_addr = addr;
	rep->re_interface = interface;
	cds_list_add(&rep->re_next, &route_list);
	return 0;
}

/*
 * Remove the specified element from the route table.
 */
int route_del(unsigned long addr)
{
	struct route_entry *rep;

	cds_list_for_each_entry(rep, &route_list, re_next) {
		if (rep->re_addr == addr) {
			cds_list_del(&rep->re_next);
			free(rep);
			return 0;
		}
	}
	return -ENOENT;
}

/*
 * Clear all elements from the route table.
 */
void route_clear(void)
{
	struct route_entry *rep;
	struct route_entry *rep1;

	cds_list_for_each_entry_safe(rep, rep1, &route_list, re_next) {
		cds_list_del(&rep->re_next);
		free(rep);
	}
}


#define route_register_thread() do { } while (0)
#define route_unregister_thread() do { } while (0)

#define quiescent_state() do { } while (0)

#define synchronize_rcu() do { } while (0)

#include "routetorture.h"
