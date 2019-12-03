/*
 * kaleidoscope.h: Definitions for managing kaleidoscopic data structures.
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

#ifndef __KALEIDOSCOPE_H
#define __KALEIDOSCOPE_H

#define KALEID_N_STATES (sizeof(void *))
#define KALEID_MASK (KALEID_N_STATES - 1)

/*
 * An kaleidoscope_group structure mediates the existence of an
 * arbitrarily large group of structures across several states.
 */
struct kaleidoscope_group {
	uintptr_t kg_state;
	struct cds_list_head kg_statelist[KALEID_N_STATES];
	struct rcu_head kg_rh;
	struct procon_mblock pm;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

/* Producer/consumer memory pool. */
DEFINE_PROCON_MPOOL(kaleidoscope_group, pm, malloc(sizeof(struct kaleidoscope_group)))

/*
 * An kaleidoscope_head structure wrappers an element of a concurrent
 * structure, preferably a structure with efficient and scalable read-mostly
 * access.  A given kaleidoscope_head structure may be associated with at
 * most one kaleidoscope_group structure at any given time.
 *
 * Normally, an kaleidoscope_head structure will be embedded into a
 * structure that also contains an element of the wrappered structure,
 * and this enclosing structure will either contain a pointer to the actual
 * element, or if the element is small and copyable, it might be included
 * directly in the enclosing structure.
 */
struct kaleidoscope_head {
	uintptr_t kh_kgi;
	struct cds_list_head kh_list;
	int (*kh_add)(struct kaleidoscope_head *khp);
	void (*kh_remove)(struct kaleidoscope_head *khp);
	void (*kh_free)(struct kaleidoscope_head *khp);
	int kh_gone;
	spinlock_t kh_lock;
	struct rcu_head kh_rh;
};

/*
 * Initialize an kaleidoscope_group structure.
 */
static inline void kaleidoscope_group_init(struct kaleidoscope_group *kgp)
{
	int i;

	kgp->kg_state = 0;
	for (i = 0; i < KALEID_N_STATES; i++)
		CDS_INIT_LIST_HEAD(&kgp->kg_statelist[i]);
}

/*
 * Get an tag from the specified state of the kaleidoscope_group structure.
 */
static inline uintptr_t
kaleidoscope_group_forstate(struct kaleidoscope_group *kgp, int state)
{
	if (kgp == NULL) {
		BUG_ON(state != 0);
		return 0;
	}
	BUG_ON(state & ~KALEID_MASK);
	BUG_ON(state & (uintptr_t)&kgp->kg_state);
	return ((uintptr_t)&kgp->kg_state) | state;
}

/*
 * Free up an kaleidoscope_group structure after a grace period has elapsed.
 * Intended to be passed to call_rcu(), and to be used externally.
 */
static inline void kaleidoscope_group_rcu_cb(struct rcu_head *rhp)
{
	struct kaleidoscope_group *kgp;
	
	kgp = container_of(rhp, struct kaleidoscope_group, kg_rh);
	kaleidoscope_group__procon_free(kgp);
}

/*
 * Does the specified structure exist?  Answered with ordering.
 * This uses Dmitry Vjukov's pointer-tagging trick.
 */
static inline int kaleidoscope_exists(struct kaleidoscope_head *khp)
{
	uintptr_t kgi = smp_load_acquire(&khp->kh_kgi);
	uintptr_t *ksp;

	if (likely(!kgi))
		return 1;
	ksp = (uintptr_t *)(kgi & ~KALEID_MASK);
	return (kgi & KALEID_MASK) == smp_load_acquire(ksp);
}

/*
 * Does the specified structure exist?  Answered without ordering,
 * otherwise the same as kaleidoscope_exists().
 */
static inline int kaleidoscope_exists_relaxed(struct kaleidoscope_head *khp)
{
	uintptr_t kgi = READ_ONCE(khp->kh_kgi);
	uintptr_t *ksp;

	if (likely(!kgi))
		return 1;
	ksp = (uintptr_t *)(kgi & ~KALEID_MASK);
	return (kgi & KALEID_MASK) == READ_ONCE(*ksp);
}

/*
 * Initialize the specified kaleidoscope_head structure.  For internal
 * use only.  External users should use kaleidoscope_head_init_perm()
 * for point insertion or kaleidoscope_head_init_state() as part of a
 * group operation.
 */
static inline void
kaleidoscope_head_init(struct kaleidoscope_head *khp,
		       uintptr_t state,
		       int (*kh_add)(struct kaleidoscope_head *khp),
		       void (*kh_remove)(struct kaleidoscope_head *khp),
		       void (*kh_free)(struct kaleidoscope_head *khp))
{
	khp->kh_kgi = state;
	CDS_INIT_LIST_HEAD(&khp->kh_list);
	khp->kh_add = kh_add;
	khp->kh_remove = kh_remove;
	khp->kh_free = kh_free;
	khp->kh_gone = 0;
	spin_lock_init(&khp->kh_lock);
}

/*
 * Initialize the specified kaleidoscope_head structure for a
 * point-insertion, where the object will be permanently present, at least
 * until the next kaleidoscope operation or point-deletion affecting it.
 */
static inline void
kaleidoscope_head_init_perm(struct kaleidoscope_head *khp,
			    int (*kh_add)(struct kaleidoscope_head *khp),
			    void (*kh_remove)(struct kaleidoscope_head *khp),
			    void (*kh_free)(struct kaleidoscope_head *khp))
{
	kaleidoscope_head_init(khp, 0, kh_add, kh_remove, kh_free);
}

/*
 * Initialize the specified kaleidoscope_head structure for insertion
 * as part of a specified state for a specified group.  If the state
 * is non-zero, the structure will initially be non-existent.  If the
 * group operation succeeds, the structure will begin its existence when
 * the group's state is set equal to that of the object.  If the group
 * operation commits to some other state, the structure will be removed
 * as part of that commit operation.
 */
static inline int
kaleidoscope_head_init_state(struct kaleidoscope_head *khp,
			     struct kaleidoscope_group *kgp,
			     int state,
			     int (*kh_add)(struct kaleidoscope_head *khp),
			     void (*kh_remove)(struct kaleidoscope_head *khp),
			     void (*kh_free)(struct kaleidoscope_head *khp))
{
	int ret;

	kaleidoscope_head_init(khp, kaleidoscope_group_forstate(kgp, state),
			       kh_add, kh_remove, kh_free);
	ret = kh_add(khp);
	if (!ret && kgp)
		cds_list_add(&khp->kh_list, &kgp->kg_statelist[state]);
	return ret;
}

/*
 * Free up an kaleidoscope_head structure after a grace period has elapsed.
 * Intended to be passed to call_rcu(), but internally only.
 */
static inline void kaleidoscope_head_rcu_cb(struct rcu_head *rhp)
{
	struct kaleidoscope_head *khp;
	
	khp = container_of(rhp, struct kaleidoscope_head, kh_rh);
	if (khp->kh_free)
		khp->kh_free(khp);
}

/*
 * Clean up the list of kaleidoscope structures that have no right to exist
 * going forward.
 */
static inline void kaleidoscope_cleanup_gone(struct kaleidoscope_head *khp)
{
	spin_lock(&khp->kh_lock);
	BUG_ON(khp->kh_gone);
	khp->kh_gone = 1;
	if (khp->kh_remove)
		khp->kh_remove(khp);
	spin_unlock(&khp->kh_lock);
	call_rcu(&khp->kh_rh, kaleidoscope_head_rcu_cb);
}

/*
 * Set the kaleidoscope state so that all the elements with the specified
 * state now exist and all other non-permanent elements cease to exist.
 */
static inline void
kaleidoscope_set_state(struct kaleidoscope_group *kgp, int state)
{
	BUG_ON(state & ~KALEID_MASK);
	smp_store_release(&kgp->kg_state, state);
}

/*
 * Commit to the current state, freeing up structures corresponding to
 * the other states.
 *
 * There is no "abort" or "rollback".  Kaleidoscopic data structures don't
 * abort!  They instead commit in a different direction!!!
 *
 * More seriously, a commit to state 0 would be similar to an abort.
 * But it all depends on the semantics that you assign to each state.
 */
static inline void kaleidoscope_commit(struct kaleidoscope_group *kgp)
{
	int i;
	struct kaleidoscope_head *khp;

	for (i = 0; i < KALEID_N_STATES; i++) {
		if (i == kgp->kg_state)
			cds_list_for_each_entry(khp, &kgp->kg_statelist[i],
						kh_list)
				smp_store_release(&khp->kh_kgi, 0);
		else
			cds_list_for_each_entry(khp, &kgp->kg_statelist[i],
						kh_list)
				kaleidoscope_cleanup_gone(khp);
	}
}

#endif /* #ifndef __KALEIDOSCOPE_H */
