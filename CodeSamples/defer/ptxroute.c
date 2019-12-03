/*
 * ptxroute.c: Demonstrate bug in my first use of RCU in DYNIX/ptx.
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
 * Copyright (c) 2015 Paul E. McKenney, IBM Corporation.-2019
 * Copyright (c) Facebook, 2019
 */

#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "../api.h"
#define _GNU_SOURCE
#define _LGPL_SOURCE
#define RCU_SIGNAL
#include <urcu.h>

/*
 * DYNIX/ptx's TCP/IP routing table extended the 1980s BSD practice.
 * The BSD's of that time used a simple linear linked list to implement the
 * routing table, but with an additional pointer to the routing entry used
 * by the last routing lookup.  The idea was that applications tended to
 * send network packets in bursts, so that the list-search overhead would
 * be amortized over all packets in that burst.
 *
 * DYNIX/ptx took the then-controversial approach of using a hash table
 * in place of the linked list, but retained the pointer to the last
 * routing lookup that was used.  I believe that this last-used pointer
 * was maintained on a per-bucket basis, but I honestly cannot remember
 * for sure.  (That was a long time ago!)  And yes, use of a hash table
 * is now commonplace, but back then it earned Ken Dove and I a couple
 * of papers.  (Both entitled "Efficient Demultiplexing of Incoming
 * TCP Packets", for whatever that might be worth.)
 *
 * And the first DYNIX/ptx data structure that I converted to RCU was
 * the TCP/IP routing table.  However, my first attempt was buggy, and
 * that bug is recreated here.  (In the original, Jan-Simon Pendry fixed
 * the bug.  And his fix was correct, despite his having no idea what
 * RCU was or how it worked.  I was suitably impressed.)
 *
 * However, a hash table is nothing more than an array of linked lists,
 * so for simplicity, this code goes back to the BSD approach.  So,
 * get your 1980s costumes out, watch a 1980s movie, and then enjoy this
 * computer-programming blast from the past!
 *
 * Your mission, should you decide to accept, is to find the bug that
 * Jan-Simon found and fix it.  There are several possible fixes.
 * No fair asking Jan-Simon!  ;-)
 */

/* Keep route entries simple with integer address and interface identifier. */
struct route_entry {
	struct cds_list_head next;
	int address;
	int interface;
};

struct cds_list_head route_head;
struct route_entry *route_cache;
DEFINE_SPINLOCK(route_lock);

/* Do a lookup and cache the result. */
int lookup(int address)
{
	struct route_entry *rep;
	int ret;

	rcu_read_lock();
	rep = rcu_dereference(route_cache);
	if (rep != NULL && rep->address == address) {
		ret = rep->interface;
		rcu_read_unlock();
		return ret;
	}
	cds_list_for_each_entry_rcu(rep, &route_head, next) {
		if (rep->address == address) {
			ret = rep->interface;
			rcu_assign_pointer(route_cache, rep);
			rcu_read_unlock();
			return ret;
		}
	}
	rcu_read_unlock();
	return -1;
}

/* Insert a new route entry. */
void insert(int address, int interface)
{
	struct route_entry *rep = malloc(sizeof(*rep));

	BUG_ON(!rep);
	rep->address = address;
	rep->interface = interface;
	spin_lock(&route_lock);
	cds_list_add_rcu(&rep->next, &route_head);
	spin_unlock(&route_lock);
}

/* Delete an existing route entry, returning zero if it was not there. */
int delete(int address)
{
	struct route_entry *rep;

	spin_lock(&route_lock);
	cds_list_for_each_entry_rcu(rep, &route_head, next) {
		if (rep->address == address) {
			cds_list_del_rcu(&rep->next);
			spin_unlock(&route_lock);
			synchronize_rcu();
			free(rep);
			return 1;
		}
	}
	spin_unlock(&route_lock);
	return 0;
}

/* Woefully inadequate test. */
int main(int argc, char *argv[])
{
	int result;

	CDS_INIT_LIST_HEAD(&route_head);
	printf("insert(5, 6)\n");
	insert(5, 6);
	printf("lookup(5)\n");
	BUG_ON(lookup(5) != 6);
	printf("delete(5)\n");
	BUG_ON(!delete(5));
	printf("lookup(5)\n");
	result = lookup(5);
	printf("lookup(5) = %d\n", result);
	return 0;
}
