/*
 * tree.c: Search tree supporting atomic move.
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
 * Copyright (c) 2014-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include <stdlib.h>
#ifdef USE_JEMALLOC
#include <jemalloc/jemalloc.h>
#endif /* #ifdef USE_JEMALLOC */
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "../../api.h"
#include "spinlockmult.h"
#include "../../lib/random.h"
#include "tree.h"
#include "treetorturetrace.h"

static inline int debugging(void)
{
#ifdef DEBUG
	return 1;
#else /* #ifdef DEBUG */
	return 0;
#endif /* #else #ifdef DEBUG */
}

#define TREE_BUG_ON(c) \
do { \
	if (debugging() && (c)) { \
		trace_dump_all_threads(); \
		abort(); \
	} \
} while (0)

static void free_treenode_cache(struct treenode *p);
static struct treenode *_tree_lookup(struct treeroot *trp, int key,
				     struct treenode **parent);

void init_treenode(struct treenode *p, int key)
{
	p->key = key;
	p->perm = 0;
	p->deleted = 0;
	p->lc = NULL;
	p->rc = NULL;
	p->data = NULL;
	p->existence = NULL;
	spin_lock_init(&p->lock);
}

/*
 * Allocate a new empty tree.  Returns NULL if out of memory.
 */
struct treeroot *tree_alloc(void)
{
	struct treeroot *trp = malloc(sizeof(*trp));

	if (!trp)
		return NULL;
	init_treenode(&trp->min, INT_MIN);
	init_treenode(&trp->max, INT_MAX);
	trp->max.perm = 1;
	trp->max.lc = &trp->min;
	trp->min.perm = 1;
	return trp;
}

/*
 * Remove all nodes from a tree, invoking the specified function on all
 * user data.  The caller must have ensured that there are no longer any
 * readers accessing the tree.
 */
static void tree_remove_all(struct treenode *cur,
			    void (*freefunc)(void *p))
{
	if (cur == NULL)
		return;
	tree_remove_all(cur->lc, freefunc);
	tree_remove_all(cur->rc, freefunc);
	if (cur->perm)
		return;
	if (cur->data && freefunc)
		freefunc(cur->data);
	free_treenode_cache(cur);
}

/*
 * Check that either an insertion happened or that the inserted node
 * was subsequently deleted.  The caller must be within an RCU read-side
 * critical section.
 */
static void tree_check_insertion(struct treeroot *trp, struct treenode *new)
{
#ifdef DEBUG
	struct treenode *cur;
	struct treenode *par;

	cur = _tree_lookup(trp, new->key, &par);
	TREE_BUG_ON(cur != new && !new->deleted);
#endif /* #ifdef DEBUG */
}

/*
 * Free an entire tree, invoking the specified function on all user data.
 * The caller must have guaranteed that there are no longer any readers
 * traversing the tree.
 */
void tree_free(struct treeroot *trp, void (*freefunc)(void *p))
{
	tree_remove_all(&trp->max, freefunc);
	free(trp);
}

/*
 * Does this node currently exist, given judgement of existence structures?
 */
static int tree_existence_exists(struct treenode *cur)
{
	return existence_exists(&cur->existence);
}

/*
 * Is this node's existence changing?
 */
static int tree_existence_changing(struct treenode *cur)
{
	return existence_is_changing(&cur->existence);
}

/*
 * Scan the specified subtree for malformation.
 */
static void tree_scan_dup_node(struct treenode *cur)
{
	struct treenode *p;

	if (cur == NULL)
		return;
	TREE_BUG_ON(tree_existence_changing(cur));
	if (cur->lc != NULL) {
		p = rcu_dereference(cur->lc);
		TREE_BUG_ON(p->key > cur->key);
		tree_scan_dup_node(p);
	}
	if (cur->rc != NULL) {
		p = rcu_dereference(cur->rc);
		TREE_BUG_ON(p->key <= cur->key);
		tree_scan_dup_node(p);
	}
}

/*
 * Scan specified tree for malformation.
 * Only one of these should be run at a time.
 */
static void tree_scan_dup(struct treeroot *trp)
{
	tree_scan_dup_node(&trp->max);
}

/*
 * Check the integrity of the specified tree.
 */
void tree_fsck(struct treeroot *trp)
{
	rcu_read_lock();
	tree_scan_dup(trp);
	rcu_read_unlock();
}

/*
 * Tree-node per-thread cache structure, which can be wired up to
 * dump excess free blocks to another such cache.  Multilevel
 * linkages are not allowed.
 */
struct treenode_cache {
	struct treenode *free;
	struct treenode **tail;
	long nfree;
	struct treenode_cache *tncp;
	spinlock_t lock __attribute__((__aligned__(CACHE_LINE_SIZE)));
	struct treenode *ffree;
	struct treenode **ftail;
	long nffree;
	struct rcu_head rh;
};

#define TREENODE_MALLOC_BATCH 32768
#define TREENODE_MALLOC_CACHE (2 * TREENODE_MALLOC_BATCH)

long __thread n_free_treenode_cache;
long __thread n_alloc_treenode_cache;
long __thread n_malloc_treenode;
long __thread n_free_treenode_cb;
struct treenode_cache __thread tnp_cache;

static void treenode_alloc_cache_init(void)
{
	spin_lock_init(&tnp_cache.lock);
	tnp_cache.tncp = NULL;
	tnp_cache.free = NULL;
	tnp_cache.tail = &tnp_cache.free;
	tnp_cache.nfree = 0;
	tnp_cache.ffree = NULL;
	tnp_cache.ftail = &tnp_cache.ffree;
	tnp_cache.nffree = 0;
}

static void free_treenode_cache(struct treenode *tnp)
{
#ifdef BAD_MALLOC
	n_free_treenode_cache++;
	struct treenode_cache *tncop;

	if (!tnp_cache.tail)
		treenode_alloc_cache_init();
	tncop = tnp_cache.tncp;
	if (tnp_cache.nfree > TREENODE_MALLOC_CACHE && tncop) {
		spin_lock(&tncop->lock);
		*(tncop->ftail) = tnp_cache.free;
		tncop->ftail = tnp_cache.tail;
		tncop->nffree += tnp_cache.nfree;
		tnp_cache.free = NULL;
		tnp_cache.tail = &tnp_cache.free;
		tnp_cache.nfree = 0;
		spin_unlock(&tncop->lock);
	}
	tnp->lc = NULL;
	*tnp_cache.tail = tnp;
	tnp_cache.tail = &tnp->lc;
	tnp_cache.nfree++;
#else /* #ifdef BAD_MALLOC */
	free(tnp);
#endif /* #else #ifdef BAD_MALLOC */
}

struct treenode_alloc {
	struct treenode tn;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

static struct treenode *alloc_treenode_cache(void)
{
#ifdef BAD_MALLOC
	int i;
	struct treenode *tnp;
	struct treenode_alloc *p;

	n_alloc_treenode_cache++;
	if (!tnp_cache.tail)
		treenode_alloc_cache_init();
	if (!tnp_cache.free && ACCESS_ONCE(tnp_cache.nffree)) {
		spin_lock(&tnp_cache.lock);
		tnp_cache.free = tnp_cache.ffree;
		tnp_cache.tail = tnp_cache.ftail;
		tnp_cache.nfree = tnp_cache.nffree;
		tnp_cache.ffree = NULL;
		tnp_cache.ftail = &tnp_cache.ffree;
		tnp_cache.nffree = 0;
		spin_unlock(&tnp_cache.lock);
	}
	if (tnp_cache.free) {
		tnp = tnp_cache.free;
		tnp_cache.free = tnp->lc;
		if (!tnp_cache.free)
			tnp_cache.tail = &tnp_cache.free;
		tnp_cache.nfree--;
		return tnp;
	}
	n_malloc_treenode++;
	p = malloc(sizeof(*p) * TREENODE_MALLOC_BATCH);
	BUG_ON(!p);
	for (i = TREENODE_MALLOC_BATCH - 1; i > 0; i--)
		free_treenode_cache(&p[i].tn);
	return &p->tn;
#else /* #ifdef BAD_MALLOC */
	n_malloc_treenode++;
	return malloc(sizeof(struct treenode));
#endif /* #else #ifdef BAD_MALLOC */
}

static void treenode_wire_call_rcu_cb(struct rcu_head *rhp)
{
	struct treenode_cache *tncwp;

	if (!tnp_cache.tail)
		treenode_alloc_cache_init();
	tncwp = container_of(rhp, struct treenode_cache, rh);
	tnp_cache.tncp = tncwp;
}

/*
 * Wire up this thread's call_rcu() thread's existence_group_cache
 * structure to this thread's structure.  Excess free existence_group
 * structures will henceforth be forwarded to the current thread.
 */
void treenode_wire_call_rcu(void)
{
	if (!tnp_cache.tail)
		treenode_alloc_cache_init();
	call_rcu(&tnp_cache.rh, treenode_wire_call_rcu_cb);
}

void treenode_cache_stats(long *nftc, long *natc, long *nmt, long *tcc)
{
	if (nftc)
		*nftc = n_free_treenode_cache;
	if (natc)
		*natc = n_alloc_treenode_cache;
	if (nmt)
		*nmt = n_malloc_treenode;
	if (tcc)
		*tcc = tnp_cache.nfree;;
}

/*
 * Allocate a node.  Leaf nodes have non-NULL data.
 */
static struct treenode *alloc_treenode(struct treeroot *trp, int key,
				       void *data, struct existence *existence)
{
	struct treenode *p = alloc_treenode_cache();

	if (!p)
		return NULL;
	init_treenode(p, key);
	p->data = data;
	p->existence = existence;
	return p;
}

/*
 * RCU callback for deferred free of tree nodes.
 */
static void tree_rcu_free_cb(struct rcu_head *rhp)
{
	struct treenode *cur = container_of(rhp, struct treenode, rh);

	free_treenode_cache(cur);
	n_free_treenode_cb++;
}

/*
 * Allocate a new internal node, dataless.  Attach the two existing
 * nodes to it.  Both treenode structures should be non-NULL.
 * After all, if there was only one node, you should stick it where
 * you plan to stick the internal node and dispense with the
 * internal node.
 */
static struct treenode *new_internal_node(struct treeroot *trp, int key,
					  struct treenode *cur,
					  struct treenode *new)
{
	struct treenode *newint = alloc_treenode(trp, key, NULL, NULL);

	if (!newint)
		return NULL;
	if (cur->key <= key) {
		newint->key = cur->key;
		newint->lc = cur;
		newint->rc = new;
	} else {
		newint->lc = new;
		newint->rc = cur;
	}
	return newint;
}

/*
 * Is the current node completely empty?
 */
static int tree_empty_node(struct treenode *cur)
{
	return cur->lc == NULL && cur->rc == NULL && cur->data == NULL;
}

/*
 * Is the current node a leaf?
 */
static int tree_leaf_node(struct treenode *cur)
{
	return cur->lc == NULL && cur->rc == NULL && cur->data != NULL;
}

/*
 * Insert the specified node at the parent's level.  This might require
 * creation of a new internal node.
 */
static int parent_insert(struct treeroot *trp, int key,
			 struct treenode *par, struct treenode *new)
{
	struct treenode *newint;
	struct treenode *old;
	struct treenode **curp;

	TREE_BUG_ON(tree_leaf_node(par)); /* Internal nodes are never leaves. */

	/* Maybe our lookup found an internal node with space... */
	if (par->lc == NULL && key <= par->key) {
		trace(trp, new, "add-leaf-lc");
		rcu_assign_pointer(par->lc, new);
		tree_check_insertion(trp, new);
		return 0;
	}
	if (par->rc == NULL && key > par->key) {
		trace(trp, new, "add-leaf-rc");
		rcu_assign_pointer(par->rc, new);
		tree_check_insertion(trp, new);
		return 0;
	}

	/* No luck, must insert a new internal node. */
	if (key <= par->key) {
		old = par->lc;
		curp = &par->lc;
	} else {
		old = par->rc;
		curp = &par->rc;
	}
	TREE_BUG_ON(old->key == key);
	newint = new_internal_node(trp, key, old, new);
	if (!newint)
		return -ENOMEM;
	if (debugging())
		spin_lock(&newint->lock);
	trace(trp, newint, "add-internal");
	trace(trp, new, "add-leaf-internal");
	trace(trp, old, "add-leaf-internal-old");
	rcu_assign_pointer(*curp, newint);
	tree_check_insertion(trp, new);
	if (debugging())
		spin_unlock(&newint->lock);
	return 0;
}

/*
 * Internal tree-lookup helper function.  This is lockless, so the
 * results are only ephemerally valid.  The caller must invoke this
 * within an RCU read-side critical section.
 */
static struct treenode *_tree_lookup(struct treeroot *trp, int key,
				     struct treenode **parent)
{
	struct treenode *cur;
	struct treenode *l;
	struct treenode *par = NULL;
	struct treenode *r;

	par = &trp->max;
	cur = &trp->min;

	/* Each pass through this loop descends one level in the tree. */
	for (;;) {
		*parent = par;
		l = rcu_dereference(cur->lc);
		r = rcu_dereference(cur->rc);
		if (cur->key == key && l == NULL && r == NULL)
			return cur;
		if (key <= cur->key) {
			if (l == NULL)
				return cur;
			par = cur;
			cur = l;
		} else {
			if (r == NULL)
				return cur;
			par = cur;
			cur = r;
		}
	}
	/* NOTREACHED */
}

/*
 * Externally visible lookup function.  The specified function, if non-NULL,
 * is invoked on the user-data pointer before dropping the tree locks.
 * Therefore, the specified function had better not acquire any lock that
 * is held while doing a traversal.  If the function is NULL, the caller
 * is responsible for guaranteeing the existence of the data, for example,
 * by invoking tree_lookup() within an RCU read-side critical section.
 */
void *tree_lookup(struct treeroot *trp, int key, void (*func)(void *data))
{
	struct treenode *cur;
	struct treenode *par;
	spinlock_t *lockp = NULL;
	int wantdelay = 0;
	int tries = 0;

retry:
	tries++;
	rcu_read_lock();
	cur = _tree_lookup(trp, key, &par);
	TREE_BUG_ON(cur == NULL);

	lockp = &cur->lock;
	spin_lock(lockp);
	if (cur->deleted)
		goto unlock_retry;
	if (!tree_leaf_node(cur) || cur->key != key) {
		cur = NULL;
		goto unlock_ret;
	}
	if (tree_existence_changing(cur))
		goto unlock_retry_delay;
	if (func)
		func(cur->data);

unlock_ret:
	spin_unlock(lockp);
	rcu_read_unlock();
	if (cur == NULL)
		return NULL;
	return cur->data;

unlock_retry_delay:
	wantdelay = 1;
unlock_retry:
	spin_unlock(lockp);
	rcu_read_unlock();
	if (wantdelay)
		poll(NULL, 0, 1);
	wantdelay = 0;
	goto retry;
}

/*
 * Tree lookup with no ordering or existence guarantees.  Caller must
 * invoke this within an RCU read-side critical section.
 */
void *tree_lookup_relaxed(struct treeroot *trp, int key)
{
	struct treenode *cur;
	struct treenode *par;

	cur = _tree_lookup(trp, key, &par);
	if (tree_leaf_node(cur) && cur->key == key && !cur->deleted &&
	    tree_existence_exists(cur)) {
		return cur->data;
	}
	return NULL;
}

/*
 * Check to see if the tree grew while we were acquiring locks.
 */
static int tree_grew(struct treenode *cur, int key)
{
	return (key <= cur->key && cur->lc != NULL) ||
	       (key > cur->key && cur->rc != NULL);
}

/*
 * Insert a node with non-standard existence.
 */
int tree_insert_existence(struct treeroot *trp, int key, void *data,
			  struct existence *node_existence, int wait)
{
	struct treenode *cur;
	struct treenode *new = NULL;
	struct treenode *par;
	int ret = 0;
	spinlock_t *lockp[2];
	int tries = 0;
	int wantdelay = 0;

	TREE_BUG_ON(data == NULL);
	new = alloc_treenode(trp, key, data, node_existence);
	if (!new)
		return -ENOMEM;
retry:
	tries++;
	rcu_read_lock();
	cur = _tree_lookup(trp, key, &par);
	TREE_BUG_ON(cur == NULL || par == NULL);

	lockp[0] = &par->lock;
	lockp[1] = &cur->lock;
	spin_lock_mult(lockp, 2);
	if (par->deleted || cur->deleted || (par->lc != cur && par->rc != cur))
		goto unlock_retry;
	if (tree_leaf_node(cur)) {
		if (cur->key == key) {
			if (tree_existence_changing(cur)) {
				if (wait)
					goto unlock_retry_delay;
				ret = -EBUSY;
			} else {
				ret = -EEXIST;
			}
			goto unlock_ret;
		}
		trace(trp, new, "parent_insert-leaf-diff-key");
		ret = parent_insert(trp, key, par, new);
		goto unlock_ret;
	}
	if (tree_grew(cur, key))
	    	goto unlock_retry;  /* Grew, go retry. */
	trace(trp, new, "parent_insert-internal");
	ret = parent_insert(trp, key, cur, new);

unlock_ret:
	trace_result(trp, cur, ret);
	spin_unlock_mult(lockp, 2);
	rcu_read_unlock();
	if (ret != 0)
		free_treenode_cache(new);
	return ret;

unlock_retry_delay:
	wantdelay = 1;
unlock_retry:
	spin_unlock_mult(lockp, 2);
	rcu_read_unlock();
	if (wantdelay) {
		poll(NULL, 0, 1);
		wantdelay = 0;
	}
	ret = 0;
	goto retry;
}

/*
 * Insert a node with standard existence.
 */
int tree_insert(struct treeroot *trp, int key, void *data)
{
	return tree_insert_existence(trp, key, data, NULL, 1);
}

/*
 * Helper function to delete the node with the specified key and
 * existence.  If the node is found, its data is returned through
 * the data pointer.
 */
static int tree_delete_existence(struct treeroot *trp, int key,
				 void **data, void *matchexistence, int wait)
{
	struct treenode *cur;
	struct treenode **p;
	struct treenode *par;
	spinlock_t *lockp[2];
	int ret = -ENOENT;
	int tries = 0;
	int wantdelay = 0;

retry:
	tries++;
	rcu_read_lock();
	cur = _tree_lookup(trp, key, &par);
	TREE_BUG_ON(cur == NULL || par == NULL);
	*data = NULL;

	lockp[0] = &par->lock;
	lockp[1] = &cur->lock;
	spin_lock_mult(lockp, 2);
	if (par->deleted || cur->deleted || (par->lc != cur && par->rc != cur))
		goto unlock_retry;
	if (tree_empty_node(cur))
		goto unlock_ret;
	if (existence_get(&cur->existence) != matchexistence) {
		if (matchexistence == NULL) {
			if (wait)
				goto unlock_retry_delay;
			ret = -EBUSY;
		}
		goto unlock_ret;
	}
	if (!tree_leaf_node(cur) || cur->key != key) {
		if (tree_grew(cur, key))
			goto unlock_retry;  /* Grew, go retry. */
	} else {
		if (par->lc == cur)
			p = &par->lc;
		else if (par->rc == cur)
			p = &par->rc;
		else
			goto unlock_retry;
		trace(trp, cur, "remove-leaf");
		rcu_assign_pointer(*p, NULL);
		cur->deleted = 1;
		*data = cur->data;
		call_rcu(&cur->rh, tree_rcu_free_cb);
		ret = 0;
	}

unlock_ret:
	trace_result(trp, cur, ret);
	spin_unlock_mult(lockp, 2);
	rcu_read_unlock();
	return ret;

unlock_retry_delay:
	wantdelay = 1;
unlock_retry:
	ret = -ENOENT; /* For next pass... */
	spin_unlock_mult(lockp, 2);
	rcu_read_unlock();
	if (wantdelay) {
		poll(NULL, 0, 1);
		wantdelay = 0;
	}
	goto retry;
}

/*
 * Delete the specified node with default existence.
 */
int tree_delete(struct treeroot *trp, int key, void **data)
{
	return tree_delete_existence(trp, key, data, NULL, 1);
}

/*
 * Helper function for the tree_map() and tree_map_relaxed() operations.
 */
static void tree_map_node(struct treeroot *trp, struct treenode *cur,
			  void (*func)(void *data, void *arg), void *arg,
			  int strict_order)
{
	if (cur == NULL)
		return;
	if (tree_leaf_node(cur)) {
		if (strict_order)
			spin_lock(&cur->lock);
		if (!cur->deleted &&
		    !tree_existence_exists(cur))
			func(cur->data, arg);
		if (strict_order)
			spin_unlock(&cur->lock);
		return;
	}
	tree_map_node(trp, rcu_dereference(cur->lc), func, arg, strict_order);
	tree_map_node(trp, rcu_dereference(cur->rc), func, arg, strict_order);
}

/*
 * Map the tree's leaves over the specified function.  The caller
 * gets to worry about handling any needed reduction step, and
 * "arg" can be useful for this purpose.  Nodes are guaranteed to
 * exist through the duration of the function call.
 */
void tree_map(struct treeroot *trp,
	      void (*func)(void *data, void *arg), void *arg)
{
	rcu_read_lock();
	tree_map_node(trp, &trp->max, func, arg, 1);
	rcu_read_unlock();
}

/*
 * Map the tree's leaves over the specified function.  The caller gets
 * to worry about handling any needed reduction step.  Nodes are -not-
 * guaranteed to exist through the duration of the function call, so the
 * caller must provide some existence guarantee.  One way to do this
 * is to free the user data under RCU control.
 */
void tree_map_relaxed(struct treeroot *trp,
		      void (*func)(void *data, void *arg), void *arg)
{
	rcu_read_lock();
	tree_map_node(trp, &trp->max, func, arg, 0);
	rcu_read_unlock();
}

/*
 * Find the leaf in the specified tree with the specified existence,
 * which might not match that of the tree.  Returns with that leaf's
 * lock held, or with non-zero return indicating the error encountered.
 * The bkout flag indicates that this call is backing out the start
 * of a failed move operation.  When this flag is set, we skip the
 * wrong-existence checks because we -know- that the element in
 * question has the wrong existence.
 */
static int tree_change_existence_find(struct treeroot *trp, int key,
				      struct treenode **cur_ap,
				      spinlock_t **lockp,
				      struct existence *ep)
{
	struct treenode *cur;
	struct treenode *par;
	int ret;

retry:
	rcu_read_lock();
	cur = _tree_lookup(trp, key, &par);
	TREE_BUG_ON(cur == NULL || par == NULL);
	*lockp = &cur->lock;
	spin_lock(*lockp);
	if (unlikely(cur->deleted)) {
		spin_unlock(*lockp);
		rcu_read_unlock();
		goto retry;
	}
	if (!tree_leaf_node(cur) || cur->key != key) {
		ret = -ENOENT;
		goto unlock_ret;
	}
	if (ep == existence_get(&cur->existence)) {
		*cur_ap = cur;
		return 0;
	}
	ret = -EBUSY;
unlock_ret:
	spin_unlock(*lockp);
	rcu_read_unlock();
	return ret;
}

/*
 * Start the process of changing a leaf node's existence by finding
 * the leaf and adding an existence structure.
 */
static int tree_existence_add(struct treeroot *trp, int key,
			      struct existence *ep, void **data)
{
	struct treenode *cur;
	spinlock_t *lockp;
	int ret = 0;

	ret = tree_change_existence_find(trp, key, &cur, &lockp, NULL);
	if (ret)
		return ret;
	existence_set(&cur->existence, ep);
	if (data)
		*data = cur->data;
	trace(trp, cur, "existence-add");
	spin_unlock(lockp);
	rcu_read_unlock();
	return ret;
}

/*
 * Complete the existence-change process, removing the node's existence
 * structure.
 */
static int tree_existence_remove(struct treeroot *trp, int key,
				 struct existence *ep)
{
	struct treenode *cur;
	spinlock_t *lockp;
	int ret;

	ret = tree_change_existence_find(trp, key, &cur, &lockp, ep);
	if (ret)
		return ret;
	existence_clear(&cur->existence);
	trace(trp, cur, "existence-remove");
	spin_unlock(lockp);
	rcu_read_unlock();
	return 0;
}

/*
 * Atomically move the specified leaf from the source tree to the
 * destination tree.
 */
int tree_atomic_move(struct treeroot *srcp, struct treeroot *dstp,
		     int key, void **data_in)
{
	struct existence_group *egp = existence_alloc();
	void *data;
	int ret, ret1;

	if (egp == NULL)
		return -ENOMEM;
	trace_move(srcp, key, NULL, "move-start");
	if (debugging() && !(random() & 0xffff)) {
		ret = -EBUSY;
		goto free_ret;
	}
	ret = tree_existence_add(srcp, key, existence_get_outgoing(egp), &data);
	if (ret) {
		trace_move(dstp, key, data, "move-abort-find");
		goto free_ret;
	}
	if (debugging() && !(random() & 0xffff)) {
		ret = -EEXIST;
		goto existence_end_ret;
	}
	ret = tree_insert_existence(dstp, key, data,
				    existence_get_incoming(egp), 0);
	if (ret) {
		trace_move(dstp, key, data, "move-abort-insert");
		goto existence_end_ret;
	}
	trace_move(dstp, key, data, "move-added");
	existence_switch(egp);
	trace_move(dstp, key, data, "existence-switched");
	ret1 = tree_delete_existence(srcp, key, &data,
				     existence_get_outgoing(egp), 0);
	TREE_BUG_ON(ret1); /* Only we can delete the old version! */
	trace_move(dstp, key, data, "deleted-old-from-src");
	ret1 = tree_existence_remove(dstp, key, existence_get_incoming(egp));
	trace_move(dstp, key, data, "removed-exist-from-new");
	TREE_BUG_ON(ret1); /* Only we can delete the new version! */
	trace_move(dstp, key, data, "move-end");
	goto free_ret;

existence_end_ret:
	ret1 = tree_existence_remove(srcp, key, existence_get_outgoing(egp));
	trace_move(dstp, key, data, "removed-exist-from-old");
	TREE_BUG_ON(ret1);
free_ret:
	existence_free(egp);
	if (data_in != NULL)
		*data_in = ret ? NULL : data;
	return ret;
}

#include "treetorture.h"
