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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include "seqlock.h"

/* Route-table entry to be included in the routing list. */
//\begin{snippet}[labelbase=ln:defer:route_seqlock:lookup,commandchars=\\\[\]]
struct route_entry {
	struct route_entry *re_next;
	unsigned long addr;
	unsigned long iface;
	int re_freed;					//\lnlbl{struct:re_freed}
};
								//\fcvexclude
struct route_entry route_list;
DEFINE_SEQ_LOCK(sl);					//\lnlbl{struct:sl}

/*
 * Look up a route entry, return the corresponding interface.
 */
unsigned long route_lookup(unsigned long addr)
{
	struct route_entry *rep;
	struct route_entry **repp;
	unsigned long ret;
	unsigned long s;

retry:							//\lnlbl{lookup:retry}
	s = read_seqbegin(&sl);				//\lnlbl{lookup:r_sqbegin}
	repp = &route_list.re_next;
	do {
		rep = READ_ONCE(*repp);
		if (rep == NULL) {
			if (read_seqretry(&sl, s))	//\lnlbl{lookup:r_sqretry1}
				goto retry;		//\lnlbl{lookup:goto_retry1}
			return ULONG_MAX;
		}
								//\fcvexclude
		/* Advance to next. */
		repp = &rep->re_next;
	} while (rep->addr != addr);
	if (READ_ONCE(rep->re_freed))			//\lnlbl{lookup:chk_freed}
		abort();				//\lnlbl{lookup:abort}
	ret = rep->iface;
	if (read_seqretry(&sl, s))			//\lnlbl{lookup:r_sqretry2}
		goto retry;				//\lnlbl{lookup:goto_retry2}
	return ret;
}
//\end{snippet}

/*
 * Add an element to the route table.
 */
//\begin{snippet}[labelbase=ln:defer:route_seqlock:add_del,commandchars=\\\[\]]
int route_add(unsigned long addr, unsigned long interface)
{
	struct route_entry *rep;

	rep = malloc(sizeof(*rep));
	if (!rep)
		return -ENOMEM;
	rep->addr = addr;
	rep->iface = interface;
	rep->re_freed = 0;			//\lnlbl{add:clr_freed}
	write_seqlock(&sl);			//\lnlbl{add:w_sqlock}
	rep->re_next = route_list.re_next;
	route_list.re_next = rep;
	write_sequnlock(&sl);			//\lnlbl{add:w_squnlock}
	return 0;
}

/*
 * Remove the specified element from the route table.
 */
int route_del(unsigned long addr)
{
	struct route_entry *rep;
	struct route_entry **repp;

	write_seqlock(&sl);				//\lnlbl{del:w_sqlock}
	repp = &route_list.re_next;
	for (;;) {
		rep = *repp;
		if (rep == NULL)
			break;
		if (rep->addr == addr) {
			*repp = rep->re_next;
			write_sequnlock(&sl);		//\lnlbl{del:w_squnlock1}
			smp_mb();
			rep->re_freed = 1;		//\lnlbl{del:set_freed}
			free(rep);
			return 0;
		}
		repp = &rep->re_next;
	}
	write_sequnlock(&sl);				//\lnlbl{del:w_squnlock2}
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

	write_seqlock(&sl);
	rep = route_list.re_next;
	WRITE_ONCE(route_list.re_next, NULL);
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
