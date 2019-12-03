/*
 * existence.h: Definitions for managing existence data structures.
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

#ifndef __EXISTENCE_H
#define __EXISTENCE_H

/* The following definitions or equivalent need to be supplied. */
// #define _LGPL_SOURCE
// #include "../../api.h"
// #define _LGPL_SOURCE
// #define RCU_SIGNAL
// #include <urcu.h>

/*
 * An existence_group structure mediates the existence of an
 * arbitrarily large group of structures.
 */
struct existence_group {
	uintptr_t eg_state;
	struct cds_list_head eg_outgoing;
	struct cds_list_head eg_incoming;
	struct rcu_head eg_rh;
	struct procon_mblock pm;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

/* Producer/consumer memory pool. */
DEFINE_PROCON_MPOOL(existence_group, pm, malloc(sizeof(struct existence_group)))

/*
 * An existence_head structure wrappers an element of a concurrent
 * structure, preferably a structure with efficient and scalable
 * read-mostly access.  A given existence_head structure may be
 * associated with at most one existence_group structure at any
 * given time.
 *
 * Normally, an existence_head structure will be embedded into
 * a structure that also contains an element of the wrappered
 * structure, and this enclosing structure will either contain a
 * pointer to the actual element, or if the element is small and
 * copyable, it might be included directly in the enclosing
 * structure.
 */
struct existence_head {
	uintptr_t eh_egi;
	struct cds_list_head eh_list;
	int (*eh_add)(struct existence_head *ehp);
	void (*eh_remove)(struct existence_head *ehp);
	void (*eh_free)(struct existence_head *ehp);
	int eh_gone;
	spinlock_t eh_lock;
	struct rcu_head eh_rh;
};

/*
 * Initialize an existence_group structure.
 */
static inline void existence_group_init(struct existence_group *egp)
{
	egp->eg_state = 0;
	CDS_INIT_LIST_HEAD(&egp->eg_outgoing);
	CDS_INIT_LIST_HEAD(&egp->eg_incoming);
}

/*
 * Get an incoming-structure tag from the specified existence_group structure.
 */
static inline uintptr_t existence_group_incoming(struct existence_group *egp)
{
	BUG_ON(ACCESS_ONCE(egp->eg_state));
	return ((uintptr_t)&egp->eg_state) | 0x1;
}

/*
 * Get an outgoing-structure tag from the specified existence_group structure.
 */
static inline uintptr_t existence_group_outgoing(struct existence_group *egp)
{
	BUG_ON(ACCESS_ONCE(egp->eg_state));
	return (uintptr_t)&egp->eg_state;
}

/*
 * Free up an existence_group structure after a grace period has elapsed.
 * Intended to be passed to call_rcu(), and to be used externally.
 */
static inline void existence_group_rcu_cb(struct rcu_head *rhp)
{
	struct existence_group *egp;
	
	egp = container_of(rhp, struct existence_group, eg_rh);
	existence_group__procon_free(egp);
}

/*
 * Does the specified structure exist?  Answered with ordering.
 * This uses Dmitry Vjukov's pointer-tagging trick.
 */
static inline int existence_exists(struct existence_head *ehp)
{
	uintptr_t egi = smp_load_acquire(&ehp->eh_egi);
	uintptr_t *esp;

	if (likely(!egi))
		return 1;
	esp = (uintptr_t *)(egi & ~0x1);
	return (egi & 0x1) == smp_load_acquire(esp);
}

/*
 * Does the specified structure exist?  Answered without ordering,
 * otherwise the same as existence_exists().
 */
static inline int existence_exists_relaxed(struct existence_head *ehp)
{
	uintptr_t egi = ACCESS_ONCE(ehp->eh_egi);
	uintptr_t *esp;

	if (likely(!egi))
		return 1;
	esp = (uintptr_t *)(egi & ~0x1);
	return (egi & 0x1) == ACCESS_ONCE(*esp);
}

/*
 * Initialize the specified existence_head structure.  For internal use
 * only.  External users should use existence_head_init_perm() or
 * existence_head_init_incoming() for point insertion and insertion
 * as part of a group operation, respectively.
 */
static inline void
existence_head_init(struct existence_head *ehp,
		    uintptr_t state,
		    int (*eh_add)(struct existence_head *ehp),
		    void (*eh_remove)(struct existence_head *ehp),
		    void (*eh_free)(struct existence_head *ehp))
{
	ehp->eh_egi = state;
	CDS_INIT_LIST_HEAD(&ehp->eh_list);
	ehp->eh_add = eh_add;
	ehp->eh_remove = eh_remove;
	ehp->eh_free = eh_free;
	ehp->eh_gone = 0;
	spin_lock_init(&ehp->eh_lock);
}

/*
 * Initialize the specified existence_head structure for a point-insertion,
 * where the object will be permanently present, at least until the
 * next existence operation or point-deletion affecting it.
 */
static inline void
existence_head_init_perm(struct existence_head *ehp,
			 int (*eh_add)(struct existence_head *ehp),
			 void (*eh_remove)(struct existence_head *ehp),
			 void (*eh_free)(struct existence_head *ehp))
{
	existence_head_init(ehp, 0, eh_add, eh_remove, eh_free);
}

/*
 * Initialize the specified existence_head structure for insertion as
 * part of a group.  The structure will thus be initially non-existent.
 * If the group operation succeeds, the structure will begin its
 * existence when that operation completes.  If the group operation
 * fails, the structure will be removed as part of the backout.
 */
static inline int
existence_head_init_incoming(struct existence_head *ehp,
			     struct existence_group *egp,
			     int (*eh_add)(struct existence_head *ehp),
			     void (*eh_remove)(struct existence_head *ehp),
			     void (*eh_free)(struct existence_head *ehp))
{
	int ret;

	existence_head_init(ehp, existence_group_incoming(egp),
			    eh_add, eh_remove, eh_free);
	ret = eh_add(ehp);
	if (!ret)
		cds_list_add(&ehp->eh_list, &egp->eg_incoming);
	return ret;
}

/*
 * Mark the specified existence_head structure as outgoing with respect
 * to the specified existence_group structure.
 */
static inline int existence_head_set_outgoing(struct existence_head *ehp,
					      struct existence_group *egp)
{
	spin_lock(&ehp->eh_lock);
	if (ehp->eh_gone) {
		spin_unlock(&ehp->eh_lock);
		return -ENOENT;
	}
	if (ehp->eh_egi) {
		spin_unlock(&ehp->eh_lock);
		return -EAGAIN;
	}
	smp_store_release(&ehp->eh_egi, existence_group_outgoing(egp));
	cds_list_add(&ehp->eh_list, &egp->eg_outgoing);
	spin_unlock(&ehp->eh_lock);
	return 0;
}

/*
 * Free up an existence_head structure after a grace period has elapsed.
 * Intended to be passed to call_rcu(), but internally only.
 */
static inline void existence_head_rcu_cb(struct rcu_head *rhp)
{
	struct existence_head *ehp;
	
	ehp = container_of(rhp, struct existence_head, eh_rh);
	if (ehp->eh_free)
		ehp->eh_free(ehp);
}

/*
 * Clean up the list of existence structures that have no right to exist
 * going forward.
 */
static inline void existence_cleanup_gone(struct existence_head *ehp)
{
	spin_lock(&ehp->eh_lock);
	BUG_ON(ehp->eh_gone);
	ehp->eh_gone = 1;
	if (ehp->eh_remove)
		ehp->eh_remove(ehp);
	spin_unlock(&ehp->eh_lock);
	call_rcu(&ehp->eh_rh, existence_head_rcu_cb);
}

/*
 * Flip the existence state so that all the incoming elements now exist
 * and all the outgoing elements cease to exist.  Then clean up the
 * outgoing objects and remove the existence-structure reference from
 * the incoming objects.
 */
static inline void existence_flip(struct existence_group *egp)
{
	struct existence_head *ehp;

	BUG_ON(ACCESS_ONCE(egp->eg_state));
	smp_store_release(&egp->eg_state, 1);
	cds_list_for_each_entry(ehp, &egp->eg_incoming, eh_list)
		smp_store_release(&ehp->eh_egi, 0);
	cds_list_for_each_entry(ehp, &egp->eg_outgoing, eh_list)
		existence_cleanup_gone(ehp);
}

/*
 * Back out of an existence operation, due to the initial state not being
 * appropriate for the operation or due to unresolvable conflict with
 * a concurrent operation.
 */
static inline void existence_backout(struct existence_group *egp)
{
	struct existence_head *ehp;

	BUG_ON(ACCESS_ONCE(egp->eg_state));
	cds_list_for_each_entry(ehp, &egp->eg_outgoing, eh_list)
		smp_store_release(&ehp->eh_egi, 0);
	cds_list_for_each_entry(ehp, &egp->eg_incoming, eh_list)
		existence_cleanup_gone(ehp);
}

#endif /* #ifndef __EXISTENCE_H */
