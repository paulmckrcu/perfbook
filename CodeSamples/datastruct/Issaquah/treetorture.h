/*
 * treetorture.h: simple performance/stress test of trees.
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

#include "stdarg.h"
#include <string.h>
#include "../../api.h"
#include "tree.h"
#include "../../lib/random.h"

/* Parameters. */
static int affinity_step;
static int duration = 1000;
static int lookupweight = 0;
static int lookuprelaxweight = 90;
static int makegraph;
static int moveweight = 1;
static int nel = 512;
static int nkeymult = 1;
static int ntracerecs;
static int nupdaters = 1;
static int every = 2;
static int one_to_one;
static int scanweight = 3;
static int updateweight = 6;
static int verbose;

/* Derived from parameters. */
static int nkeys;
static long addrand;
static long delrand;
static long lookuprand;
static long lookuprelaxrand;
static long moverand;
static long scanrand;

struct el {
	atomic_t state;
	int key;
	int dup;
	atomic_t gen;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));
/* ->state values. */
#define EL_OUT		0x0
#define EL_IN		0x1
#define EL_MASK		0x1

#ifdef DEBUG_TRACE

struct trace_rec {
	struct treeroot *tree;
	void *existence;
	int key;
	void *data;
	int state;
	int gen;
	char opname[32];
	char *filename;
	const char *func;
	int lineno;
};

struct trace_group {
	int me;
	struct trace_rec *tr;
	int *tr_idx;
	struct trace_group *next;
};

static struct trace_rec __thread *tr;
static struct trace_group __thread tr_mine;
static struct trace_group *tr_first;
static int __thread tr_idx;
DEFINE_SPINLOCK(td_mutex);
static int tr_enable;

static void tracing_init(int me)
{
	tr = malloc(sizeof(*tr) * ntracerecs);
	if (!tr)
		abort();
	tr_mine.me = me;
	tr_mine.tr = tr;
	tr_mine.tr_idx = &tr_idx;
	spin_lock(&td_mutex);
	tr_mine.next = tr_first;
	tr_first = &tr_mine;
	spin_unlock(&td_mutex);
}

static void tracing_enable(void)
{
	tr_enable = !!ntracerecs;
}

static void tracing_disable(void)
{
	tr_enable = 0;
}

static void _trace(struct treeroot *t, struct treenode *tnp, char *on,
		   char *file, const char *const f, int ln)
{
	if (tr_enable && tr) {
		struct el *elp = tnp->data;

		tr[tr_idx].tree = t;
		tr[tr_idx].existence =
			existence_get(&tnp->existence);
		tr[tr_idx].key = tnp->key;
		tr[tr_idx].data = tnp->data;
		if (elp == NULL) {
			tr[tr_idx].state = 0;
			tr[tr_idx].gen = 0;
		} else {
			tr[tr_idx].state = atomic_read(&elp->state);
			tr[tr_idx].gen = atomic_inc_return(&elp->gen);
		}
		strncpy(tr[tr_idx].opname, on, 32);
		tr[tr_idx].filename = file;
		tr[tr_idx].func = f;
		tr[tr_idx].lineno = ln;
		if (++tr_idx >= ntracerecs)
			tr_idx = 0;
	}
}

static void trace_dump_thread(struct trace_group *tgp)
{
	int i;
	struct trace_rec *p;

	if (!tr)
		return;
	spin_lock(&td_mutex);
	printf("Thread %d trace[%d]:\n", tgp->me, *tgp->tr_idx);
	for (i = 0; i < ntracerecs; i++) {
		p = &tgp->tr[i];
		if (p->opname == NULL)
			continue;
		printf("%#lx%c %d %#lx %d %d %s %s %s %d\n",
		       (unsigned long)p->tree, p->existence ? '!' : ' ',
		       p->key, (unsigned long)p->data,
		       p->gen, p->state, p->opname,
		       p->filename, p->func, p->lineno);
	}
	spin_unlock(&td_mutex);
}

void trace_dump_all_threads(void)
{
	struct trace_group *tgp;

	for (tgp = tr_first; tgp != NULL; tgp = tgp->next) {
		trace_dump_thread(tgp);
	}
}

#else /* #ifdef DEBUG_TRACE */

void trace_dump_all_threads(void)
{
}

#endif /* #else #ifdef DEBUG_TRACE */

static int el_is_in(struct el *elp)
{
	return atomic_read(&elp->state) & 0x1;
}

static int el_is_out(struct el *elp)
{
	return !(atomic_read(&elp->state) & 0x1);
}

static void put_el_in(struct el *elp)
{
	int newval = atomic_inc_return(&elp->state);

	TREE_BUG_ON((newval & EL_MASK) != EL_IN);
}

static void put_el_out(struct el *elp)
{
	int newval = atomic_inc_return(&elp->state);

	TREE_BUG_ON((newval & EL_MASK) != EL_OUT);
}

struct el *el_array;

void dump_node(struct treenode *cur, int level)
{
	int i;

	if (cur == NULL)
		return;
	for (i = 0; i < level; i++)
		printf("\t");
	printf("Node %#lx: %d %#lx %c (%#lx, %#lx)\n",
	       (unsigned long)cur, cur->key, (unsigned long)cur->data,
	       cur->existence == NULL
			? '.'
			: "IO"[existence_is_outgoing(&cur->existence)],
	       (unsigned long)cur->lc, (unsigned long)cur->rc);
	dump_node(cur->lc, level + 1);
	dump_node(cur->rc, level + 1);
}

/*
 * Dump ASCII representation of the tree.
 */
void dump_tree(struct treeroot *trp)
{
	printf("Tree %#lx\n", (unsigned long)trp);
	dump_node(&trp->max, 1);
}

void graphviz_node(struct treenode *par, struct treenode *cur)
{
	char *cp = "";

	if (cur == NULL)
		return;
	if (par != NULL)
		printf("\t\"%#lx\" -> \"%#lx\";\n",
		       (unsigned long)par, (unsigned long)cur);
	if (cur->data != NULL)
		cp = "peripheries=2";
	printf("\t\"%#lx\" [label=\"%#lx: %d %#lx\",%s];\n",
	       (unsigned long)cur, (unsigned long)cur, cur->key,
	       (unsigned long)cur->data, cp);
	graphviz_node(cur, cur->lc);
	graphviz_node(cur, cur->rc);
}

/*
 * Dump out the tree in .dot file format for graphviz.
 */
void graphviz_tree(struct treeroot *trp)
{
	printf("digraph tree {\n");
	printf("\tsize = \"6,6\"\n");
	printf("\tnode [shape=ellipse, fontsize=10]\n");
	graphviz_node(NULL, &trp->max);
	printf("}\n");
}

/*
 * Free-function that doesn't free anything.  It instead exercises
 * callback code paths.
 */
static void dumb_freefunc(void *p)
{
	if (verbose)
		printf("dumb_freefunc(%#lx)\n", (unsigned long)p);
}

/*
 * Look up an element and scream if it is not found.
 */
static void tree_lookup_expected(struct treeroot *trp, int key)
{
	void *data;

	rcu_read_lock();
	data = tree_lookup(trp, key, dumb_freefunc);
	if (tree_lookup_relaxed(trp, key) != data)
		printf("Mismatch!!! tree_lookup() vs. tree_lookup_relaxed()\n");
	if (data) {
		if (verbose)
			printf("Found %#lx\n", (unsigned long)data);
	} else {
		printf("Not found!!! %d\n", key);
		abort();
	}
	rcu_read_unlock();
}

/*
 * Look up the node, scream if it is found.
 */
void tree_lookup_unexpected(struct treeroot *trp, int key)
{
	void *data;

	rcu_read_lock();
	data = tree_lookup(trp, key, dumb_freefunc);
	if (tree_lookup_relaxed(trp, key) != data)
		printf("Mismatch!!! tree_lookup() vs. tree_lookup_relaxed()\n");
	if (data) {
		printf("Found!!! %d -> %#lx\n", key, (unsigned long)data);
		abort();
	} else {
		if (verbose)
			printf("Not found (as expected) %d\n", key);
	}
	rcu_read_unlock();
}

/*
 * Insert a node into the tree, where it is known that no such node
 * exists in the tree, and where no one is concurrently inserting
 * a node with the same key.
 */
int do_insert(struct treeroot *trp, int key, void *p)
{
	int ret;

	if (verbose)
		printf("tree_insert(%d)...\n", key);
	if (p == NULL)
		p = (void *)(long)(key * 0x10001);
	ret = tree_insert(trp, key, p);
	if (ret) {
		if (verbose)
			printf("tree_insert(%d) returned %d (%s)\n",
			       key, ret, strerror(-ret));
		return ret;
	}
	rcu_read_lock();
	if (verbose)
		dump_tree(trp);
	tree_lookup_expected(trp, key);
	rcu_read_unlock();
	return ret;
}

/*
 * Delete an element known to be in the tree, and where it is also
 * known that no one else will be concurrently deleting it.
 */
int do_delete(struct treeroot *trp, int key, void **p)
{
	void *data;
	int ret;

	ret = tree_delete(trp, key, &data);
	if (ret) {
		if (verbose)
			printf("tree_delete(%d) failed: %d (%s)\n",
			       key, ret, strerror(-ret));
	} else {
		if (verbose)
			printf("tree_delete(%d) -> %#lx\n", key,
			       (unsigned long)data);
	}
	rcu_read_lock();
	if (verbose)
		dump_tree(trp);
	tree_lookup_unexpected(trp, key);
	rcu_read_unlock();
	if (p)
		*p = data;
	return ret;
}

/*
 * Move an element from one tree to the other.  If expected_ret>0,
 * don't do error-checking.  Hint: If there are other threads running
 * that could possibly touch this key, you really don't want error
 * checking!
 */
static void do_atomic_move(struct treeroot *trp0, struct treeroot *trp1,
			   int key, void **data_in, int expected_ret)
{
	void *data = NULL;
	int ret;

	ret = tree_atomic_move(trp0, trp1, key, &data);
	if (verbose)
		printf("tree_atomic_move(trp0, trp1, key, %#lx) -> %d\n",
		       (unsigned long)data, ret);
	if (expected_ret <= 0) {
		TREE_BUG_ON(ret != expected_ret);
		if (!ret) {
			tree_lookup_unexpected(trp0, key);
			tree_lookup_expected(trp1, key);
		} else if (ret == -ENOENT) {
			tree_lookup_unexpected(trp0, key);
		} else if (ret == -EEXIST) {
			if (trp0 != trp1)
				tree_lookup_expected(trp0, key);
			tree_lookup_expected(trp1, key);
		}
	}
	if (verbose) {
		dump_tree(trp0);
		dump_tree(trp1);
	}
	if (data_in != NULL)
		*data_in = data;
}

/*
 * manual smoke test, small tree.
 */
void manual_smoke(void)
{
	struct existence_group *egp;
	void *data;
	int ret;
	struct treeroot *trp0;
	struct treeroot *trp1;

	trp0 = tree_alloc();
	TREE_BUG_ON(trp0 == NULL);
	if (verbose)
		dump_tree(trp0);
	do_insert(trp0, 4, NULL);
	do_insert(trp0, 4, NULL);
	do_insert(trp0, 8, NULL);
	do_insert(trp0, 2, NULL);
	do_insert(trp0, 6, NULL);
	do_insert(trp0, 9, NULL);
	do_insert(trp0, 10, NULL);
	do_insert(trp0, 11, NULL);
	do_insert(trp0, 5, NULL);
	do_insert(trp0, 3, NULL);
	do_insert(trp0, 7, NULL);
	tree_lookup_unexpected(trp0, 1);
	do_insert(trp0, 1, NULL);
	do_delete(trp0, 9, NULL);
	do_delete(trp0, 5, NULL);
	do_delete(trp0, 6, NULL);
	do_delete(trp0, 7, NULL);
	do_delete(trp0, 8, NULL);
	if (makegraph)
		graphviz_tree(trp0);

	trp1 = tree_alloc();
	TREE_BUG_ON(trp1 == NULL);
	do_atomic_move(trp0, trp1, 11, NULL, 0);
	do_atomic_move(trp0, trp1, 4, NULL, 0);
	do_atomic_move(trp1, trp0, 4, NULL, 0);
	do_atomic_move(trp0, trp0, 4, NULL, -EBUSY);
	do_atomic_move(trp1, trp1, 4, NULL, -ENOENT);
	do_atomic_move(trp1, trp0, 4, NULL, -ENOENT);
	do_insert(trp0, 11, NULL);
	do_atomic_move(trp0, trp1, 11, NULL, -EEXIST);
	do_atomic_move(trp1, trp0, 11, NULL, -EEXIST);
	egp = existence_alloc();
	TREE_BUG_ON(!egp);
	ret = tree_existence_add(trp0, 11, existence_get_outgoing(egp), &data);
	TREE_BUG_ON(ret);
	ret = tree_delete_existence(trp0, 11, &data, NULL, 0);
	TREE_BUG_ON(ret != -EBUSY);
	ret = tree_insert_existence(trp0, 11, (void *)0xb000b, NULL, 0);
	TREE_BUG_ON(ret != -EBUSY);
	do_atomic_move(trp1, trp0, 11, NULL, -EBUSY);
	do_atomic_move(trp0, trp1, 11, NULL, -EBUSY);
	ret = tree_delete_existence(trp0, 11, &data,
				    existence_get_outgoing(egp), 0);
	TREE_BUG_ON(ret);
	ret = tree_insert_existence(trp0, 11, (void *)0xb000b,
				    existence_get_incoming(egp), 0);
	TREE_BUG_ON(ret);
	ret = tree_delete_existence(trp0, 11, &data, NULL, 0);
	TREE_BUG_ON(ret != -EBUSY);
	ret = tree_insert_existence(trp0, 11, (void *)0xb000b, NULL, 0);
	TREE_BUG_ON(ret != -EBUSY);

	tree_free(trp0, dumb_freefunc);
	tree_free(trp1, dumb_freefunc);
	existence_free(egp);
}

/*
 * Insert the specified element and key, and gripe if already present.
 */
static void init_insert_unique(struct treeroot *trp, struct el *elp, int key,
			       int check)
{
	int ret;

	elp->key = key;
	elp->dup = 0;
	ret = do_insert(trp, elp->key, elp);
	if (!check)
		return;
	if (ret == 0)
		put_el_in(elp);
	else
		TREE_BUG_ON(1);
}

/*
 * Spread the specified range of elements, inserting them in order
 * so as to balance the tree.
 */
static void spread_key_range(struct treeroot *trp, struct el *elp,
			     int low, int high, int check)
{
	int mid;

	if (high == low) {
		init_insert_unique(trp, &elp[low], low, check);
		return;
	}
	mid = (low + high) / 2;
	if (mid == low) {
		init_insert_unique(trp, &elp[low], low, check);
		init_insert_unique(trp, &elp[high], high, check);
		return;
	}
	init_insert_unique(trp, &elp[mid], mid, check);
	spread_key_range(trp, elp, mid + 1, high, check);
	spread_key_range(trp, elp, low, mid - 1, check);
}

/*
 * Initialize the array of elements, using the tree to check for
 * duplicates.
 */
void init_el_array(struct treeroot *trp, struct el *elp, int nel, int nkeys)
{
	int i;

	if (one_to_one) {
		spread_key_range(trp, elp, 0, nel - 1, 1);
		return;
	}
	for (i = 0; i < nel; i++) {
		el_array[i].key = random() % nkeys;
		el_array[i].dup = 0;
		atomic_set(&el_array[i].gen, 0);
		if (do_insert(trp, el_array[i].key, &el_array[i]) == 0) {
			/* Successfully inserted. */
			atomic_set(&el_array[i].state, EL_IN);
		} else {
			atomic_set(&el_array[i].state, EL_OUT);
			el_array[i].dup = 1;
			elp = tree_lookup(trp, el_array[i].key, NULL);
			TREE_BUG_ON(!elp);
			elp->dup = 1;
		}
	}
}

/*
 * Automated random smoke test, medium tree.
 */
void auto_smoke(void)
{
	struct el *elp;
	int i;
	struct treeroot *trp;

	trp = tree_alloc();
	TREE_BUG_ON(trp == NULL);
	el_array = malloc(nel * sizeof(*el_array));
	TREE_BUG_ON(el_array== NULL);

	/* Load up the tree, checking for duplicates. */
	init_el_array(trp, &el_array[0], nel, nkeys);

	/* Check insertions. */
	for (i = 0; i < nel; i++) {
		elp = tree_lookup(trp, el_array[i].key, NULL);
		TREE_BUG_ON(elp == &el_array[i] &&
		       (elp != NULL) !=
		       el_is_in(&el_array[i]));
		TREE_BUG_ON(elp == NULL && !el_array[i].dup);
	}

	tree_free(trp, dumb_freefunc);
	free(el_array);
}

/*
 * Insert an element that might have conflicting trees and concurrent
 * deletions.
 */
int do_insert_el(struct treeroot *trp, int key, struct el *elp)
{
	int ret;

	if (el_is_in(elp))
		return -EBUSY;  /* In tree, others might do something. */
	put_el_in(elp);
	ret = tree_insert(trp, key, elp);
	if (ret == 0)
		return ret; /* Success! */

	/*
	 * Failure means we need to back out our ->state update.
	 * This is safe because the element is not in the tree,
	 * which means that no one else will mess with it.  We still
	 * test conflicting insertions because we have duplicate keys.
	 */
	put_el_out(elp);
	return ret;
}

/*
 * Delete an element that is subject to concurrent deletion by others.
 */
int do_delete_el(struct treeroot *trp, int key, struct el *elp, void **p)
{
	void *data;
	int ret;
	struct el *elp1 = elp;

	ret = tree_delete(trp, key, &data);
	if (ret != 0 || data != elp) {
		if (ret != 0) {
			*p = NULL;
			return ret;
		}
	}

	/* We succeeded in deleting something, maybe ours... */
	if (data != elp)
		elp1 = data;
	put_el_out(elp1);
	*p = elp1;
	return 0;
}

/*
 * Check a struct el to make sure that it is where it is supposed to
 * be.  Call this after everything has quiesced, as you can get false
 * positives while in the midst of a run.
 */
static char *do_check_el(struct treeroot *trp, struct el *elp)
{
	void *data;
	char *cp = NULL;

	rcu_read_lock();
	data = tree_lookup_relaxed(trp, elp->key);
	if (el_is_in(elp) && data != elp)
		cp = "EL_IN not in tree or being moved";
	else if (el_is_out(elp) && data == elp)
		cp = "EL_OUT in tree";
	rcu_read_unlock();
	return cp;
}

static void do_check_all_el(struct treeroot *trp, struct el *elp, int n)
{
	int i;
	int j;
	char *ret;

	for (i = 0; i < n; i++) {
		ret = do_check_el(trp, &elp[i]);
		if (ret != NULL) {
			printf("Element %d, ret=\"%s\"\n", i, ret);
			for (j = 0; j < n; j++)
				printf("%3d: %#lx state=%d key=%d dup=%d\n",
				       j, (unsigned long)&elp[j],
				       atomic_read(&elp[j].state),
				       elp[j].key, elp[j].dup);
			dump_tree(trp);
			fflush(stdout);
			abort();
		}
	}
	return;
}

/*
 * Stress-test control.
 */
atomic_t nthreads_running;
atomic_t nthreads_done;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

/*
 * Child-control/reporting structure.
 */
struct child {
	struct treeroot *trp0;
	struct treeroot *trp1;
	struct el *elbase;
	int nel;
	int me;
	long long insattempts;
	long long insfailures;
	long long insfaildups;
	long long lookupattempts;
	long long lookupfailures;
	long long delattempts;
	long long delothers;
	long long delfailures;
	long long delfaildups;
	long long moveattempts;
	long long movefailures;
	long long movebackmemfailure;
	long long movebackdupfailure;
	long long scanattempts;
	long long n_free_treenode_cache;
	long long n_alloc_treenode_cache;
	long long n_malloc_treenode;
	long long n_treenode_cache_count;
};

void mapfunc(void *data, void *arg)
{
	struct el *elp = data;
	int *i = arg;

	*i += elp->key;
}

struct cbs_wait {
	int rcu_done;
	struct rcu_head rh;
};

static void wait_for_cbs(struct rcu_head *rhp)
{
	struct cbs_wait *cwp = container_of(rhp, struct cbs_wait, rh);

	smp_mb();
	ACCESS_ONCE(cwp->rcu_done) = 1;
}

/*
 * Wait for current thread's RCU CBs to drain.  This avoids bugs in
 * old userspace RCU implementations, but also ensures that RCU callback
 * overhead is correctly accounted for.
 */
void wait_for_my_rcu_cbs(struct cbs_wait *cwp)
{
	cwp->rcu_done = 0;
	call_rcu(&cwp->rh, wait_for_cbs);
	while (!ACCESS_ONCE(cwp->rcu_done))
		poll(NULL, 0, 1);
}

/*
 * Child thread for stress test.
 */
void *tree_stress_test_child(void *arg)
{
	struct child *cp = arg;
	struct call_rcu_data *crdp;
	struct cbs_wait cw;
	struct el *elp;
	struct el *elp1;
	int i;
	long oprand;
	int ret;
	long long insattempts = 0LL;
	long long insfailures = 0LL;
	long long insfaildups = 0LL;
	long long lookupattempts = 0LL;
	long long lookupfailures = 0LL;
	long long delattempts = 0LL;
	long long delothers = 0LL;
	long long delfailures = 0LL;
	long long delfaildups = 0LL;
	long long moveattempts = 0LL;
	long long movefailures = 0LL;
	long long movebackmemfailure = 0LL;
	long long movebackdupfailure = 0LL;
	long long scanattempts = 0LL;
	long nftc;
	long natc;
	long nmt;
	long tcc;

	srandom(time(NULL));
	rcu_register_thread();
	if (affinity_step) {
		i = affinity_step * cp->me;
		run_on(i);
		crdp = create_call_rcu_data(0, i);
	} else {
		crdp = create_call_rcu_data(0, -1);
	}
	set_thread_call_rcu_data(crdp);
	existence_wire_call_rcu();
	treenode_wire_call_rcu();
	tracing_init(cp->me);
	atomic_inc(&nthreads_running);
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		i = random() % cp->nel;
		elp = &cp->elbase[i];
		if (every && (elp->key % every))
			continue;
		oprand = random() & 0xffff;
		if (oprand < addrand) {
			insattempts++;
			ret = do_insert_el(cp->trp0, elp->key, elp);
			if (ret) {
				if (elp->dup)
					insfaildups++;
				else
					insfailures++;
			}
		} else if (oprand < delrand) {
			delattempts++;
			ret = do_delete_el(cp->trp0, elp->key,
					   elp, (void **)&elp1);
			if (ret) {
				if (elp->dup)
					delfaildups++;
				else
					delfailures++;
			} else if (elp != elp1) {
				delothers++;
			}
		} else if (oprand < lookuprand) {
			lookupattempts++;
			rcu_read_lock();
			if (tree_lookup(cp->trp0, elp->key, NULL))
				lookupfailures++;
			rcu_read_unlock();
		} else if (oprand < lookuprelaxrand) {
			lookupattempts++;
			rcu_read_lock();
			if (tree_lookup_relaxed(cp->trp0, elp->key))
				lookupfailures++;
			rcu_read_unlock();
		} else if (oprand < moverand) {
			moveattempts++;
			if (tree_atomic_move(cp->trp0, cp->trp1,
					     elp->key, NULL)) {
				movefailures++;
				continue;
			}
			for (;;) {
				ret = tree_atomic_move(cp->trp1, cp->trp0,
						       elp->key, NULL);
				if (ret == 0)
					break;
				if (ret == -ENOENT)
					abort();
				if (ret == -ENOMEM) {
					movebackmemfailure++;
					poll(NULL, 0, 1);
					continue;
				}
				if (ret == -EEXIST || ret == -EBUSY) {
					movebackdupfailure++;
					ret = do_delete_el(cp->trp0, elp->key,
							   elp, (void **)&elp1);
					if (ret == -EEXIST)
						poll(NULL, 0, 1);
				}
			}
		} else {
			scanattempts++;
			tree_map_relaxed(cp->trp0, mapfunc, &i);
		}
		/* If you put something here, mind the "continue" statements! */
	}
	rcu_unregister_thread();
	cp->insattempts = insattempts;
	cp->insfailures = insfailures;
	cp->insfaildups = insfaildups;
	cp->lookupattempts = lookupattempts;
	cp->lookupfailures = lookupfailures;
	cp->delattempts = delattempts;
	cp->delothers = delothers;
	cp->delfailures = delfailures;
	cp->delfaildups = delfaildups;
	cp->moveattempts = moveattempts;
	cp->movefailures = movefailures;
	cp->movebackmemfailure = movebackmemfailure;
	cp->movebackdupfailure = movebackdupfailure;
	cp->scanattempts = scanattempts;
	treenode_cache_stats(&nftc, &natc, &nmt, &tcc);
	cp->n_free_treenode_cache = nftc;
	cp->n_alloc_treenode_cache = natc;
	cp->n_malloc_treenode = nmt;
	cp->n_treenode_cache_count = tcc;
#ifdef DEBUG_TRACE
	trace_dump_thread(&tr_mine);
#endif /* #ifdef DEBUG_TRACE */
	wait_for_my_rcu_cbs(&cw);
	atomic_inc(&nthreads_done);
	set_thread_call_rcu_data(NULL);
	call_rcu_data_free(crdp);
	return NULL;
}

/*
 * Pass this to tree_map_relaxed() when the tree is supposed to be empty.
 */
void do_tree_die(void *data, void *arg)
{
	abort();
}

void tree_stress_test(void)
{
	int eb_next = 0;
	struct child *cp = malloc(sizeof(*cp) * nupdaters);
	int i;
	int nelpc;
	long long starttime;
	struct treeroot *trp0;
	struct treeroot *trp1;
	long long insattempts = 0LL;
	long long insfailures = 0LL;
	long long insfaildups = 0LL;
	long long lookupattempts = 0LL;
	long long lookupfailures = 0LL;
	long long delattempts = 0LL;
	long long delothers = 0LL;
	long long delfailures = 0LL;
	long long delfaildups = 0LL;
	long long moveattempts = 0LL;
	long long movefailures = 0LL;
	long long movebackmemfailure = 0LL;
	long long movebackdupfailure = 0LL;
	long long scanattempts = 0LL;
	long long n_free_treenode_cache = 0LL;
	long long n_alloc_treenode_cache = 0LL;
	long long n_malloc_treenode = 0LL;
	long long n_treenode_cache_count = 0LL;
	int totalweight;

	TREE_BUG_ON(nel < nupdaters);
	TREE_BUG_ON(cp == NULL);

	totalweight = lookupweight + lookuprelaxweight + moveweight +
		      scanweight + updateweight;
	addrand = updateweight * 65536 / totalweight / 2;
	delrand = addrand + updateweight * 65536 / totalweight / 2;
	lookuprand = delrand + lookupweight * 65536 / totalweight;
	lookuprelaxrand = lookuprand + lookuprelaxweight * 65536 / totalweight;
	moverand = lookuprelaxrand + moveweight * 65536 / totalweight;
	scanrand = moverand + scanweight * 65536 / totalweight;
/*&&&&*/printf("totalweight: %d lookupweight: %d lookuprelaxweight: %d moveweight: %d scanweight: %d updateweight: %d\n",
	       totalweight, lookupweight, lookuprelaxweight, moveweight, scanweight, updateweight);
/*&&&&*/printf("addrand: %ld delrand: %ld lookuprand: %ld lookuprelaxrand: %ld moverand: %ld scanrand: %ld\n",
	       addrand, delrand, lookuprand, lookuprelaxrand, moverand, scanrand);

	tracing_enable();

	trp0 = tree_alloc();
	TREE_BUG_ON(trp0 == NULL);
	trp1 = tree_alloc();
	TREE_BUG_ON(trp1 == NULL);
	el_array = malloc(nel * sizeof(*el_array));
	TREE_BUG_ON(el_array== NULL);
	nelpc = nel / nupdaters;

	/* Load up the tree, checking for duplicates. */
	init_el_array(trp0, &el_array[0], nel, nkeys);
	if (one_to_one) {
		spread_key_range(trp1, el_array, 0, nel - 1, 0);
		for (i = 0; i < nel; i++) {
			void *data;

			if (every && !(el_array[i].key % every))
				tree_delete(trp1, el_array[i].key, &data);
		}
	}
	if (makegraph) {
		graphviz_tree(trp0);
		if (one_to_one)
			graphviz_tree(trp1);
	}

	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nupdaters; i++) {
		cp[i].trp0 = trp0;
		cp[i].trp1 = trp1;
		cp[i].elbase = &el_array[eb_next];
		eb_next += nelpc;
		cp[i].nel = eb_next <= nel ? nelpc : nelpc - (eb_next - nel);
		cp[i].me = i;
		cp[i].insattempts = 0LL;
		cp[i].insfailures = 0LL;
		cp[i].insfaildups = 0LL;
		cp[i].lookupattempts = 0LL;
		cp[i].lookupfailures = 0LL;
		cp[i].delattempts = 0LL;
		cp[i].delothers = 0LL;
		cp[i].delfailures = 0LL;
		cp[i].delfailures = 0LL;
		cp[i].moveattempts = 0LL;
		cp[i].movefailures = 0LL;
		cp[i].movebackmemfailure = 0LL;
		cp[i].movebackdupfailure = 0LL;
		cp[i].scanattempts = 0LL;
		cp[i].n_free_treenode_cache = 0LL;
		cp[i].n_alloc_treenode_cache = 0LL;
		cp[i].n_malloc_treenode = 0LL;
		create_thread(tree_stress_test_child, &cp[i]);
	}

	/* Wait for all threads to initialize. */
	while (atomic_read(&nthreads_running) < nupdaters)
		poll(NULL, 0, 1);
	smp_mb();

	/* Run the test. */
	starttime = get_microseconds();
	ACCESS_ONCE(goflag) = GOFLAG_RUN;
	poll(NULL, 0, duration);
	ACCESS_ONCE(goflag) = GOFLAG_STOP;
	while (atomic_read(&nthreads_done) < nupdaters)
		poll(NULL, 0, 1);
	starttime = get_microseconds() - starttime;
	printf("Duration: %lld microseconds\n", starttime);
	wait_all_threads();

	if (debugging()) {
		/* Validate trees at end of test. */
		tree_fsck(trp0);
		do_check_all_el(trp0, el_array, nel);
		/* For do_check_all_el() to pass, trp1 must be empty, but... */
		if (!one_to_one || every <= 1)
			tree_map_relaxed(trp1, do_tree_die, NULL);
	}

	/* Summarize results and output them. */
	for (i = 0; i < nupdaters; i++) {
		insattempts += cp[i].insattempts;
		insfailures += cp[i].insfailures;
		insfaildups += cp[i].insfaildups;
		lookupattempts += cp[i].lookupattempts;
		lookupfailures += cp[i].lookupfailures;
		delattempts += cp[i].delattempts;
		delothers += cp[i].delothers;
		delfailures += cp[i].delfailures;
		delfaildups += cp[i].delfaildups;
		moveattempts += cp[i].moveattempts;
		movefailures += cp[i].movefailures;
		movebackmemfailure += cp[i].movebackmemfailure;
		movebackdupfailure += cp[i].movebackdupfailure;
		scanattempts += cp[i].scanattempts;
		n_free_treenode_cache += cp[i].n_free_treenode_cache;
		n_alloc_treenode_cache += cp[i].n_alloc_treenode_cache;
		n_malloc_treenode += cp[i].n_malloc_treenode;
		n_treenode_cache_count += cp[i].n_treenode_cache_count;
	}
	printf("lookups: %lld %lld scans: %lld ins: %lld %lld %lld  del: %lld %lld %lld %lld moves: %lld %lld %lld %lld allocstats: %lld %lld %lld %lld\n",
	       lookupattempts, lookupfailures, scanattempts,
	       insattempts, insfailures, insfaildups,
	       delattempts, delothers, delfailures, delfaildups,
	       moveattempts, movefailures,
	       movebackmemfailure, movebackdupfailure,
	       n_free_treenode_cache, n_alloc_treenode_cache,
	       n_malloc_treenode, n_treenode_cache_count);
	tree_free(trp0, NULL);
	tree_free(trp1, NULL);
	free(el_array);
	free(cp);
	tracing_disable();
}

static void smoketest(void)
{
	rcu_register_thread();
	manual_smoke();
	auto_smoke();
	rcu_unregister_thread();
}

struct rcumalloc_sut {
	long long *n_free_ptr;
	struct rcu_head rh;
};

struct rcumalloc_child {
	int me;
	long long n_mallocs;
	long long n_malloc_fails;
	long long n_frees __attribute__((__aligned__(CACHE_LINE_SIZE)));
};

/* Free it and count it! */
void tree_rcumalloc_rcu(struct rcu_head *rhp)
{
	struct rcumalloc_sut *rsp = container_of(rhp, struct rcumalloc_sut, rh);

	(*rsp->n_free_ptr)++;
	free(rsp);
}

/*
 * Child thread for rcu_malloc test.
 */
void *tree_rcumalloc_child(void *arg)
{
	struct rcumalloc_child *cp = arg;
	struct call_rcu_data *crdp;
	struct cbs_wait cw;
	int i;
	struct rcumalloc_sut *rsp;

	rcu_register_thread();
	if (affinity_step) {
		i = affinity_step * cp->me;
		run_on(i);
		crdp = create_call_rcu_data(0, i);
	} else {
		crdp = create_call_rcu_data(0, -1);
	}
	set_thread_call_rcu_data(crdp);
	tracing_init(cp->me);
	atomic_inc(&nthreads_running);
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		cp->n_mallocs++;
		rsp = malloc(sizeof(*rsp));
		if (rsp == NULL) {
			cp->n_malloc_fails++;
			poll(NULL, 0, 1);
			continue;
		}
		rsp->n_free_ptr = &cp->n_frees;
		call_rcu(&rsp->rh, tree_rcumalloc_rcu);
		/* If you put something here, mind the "continue" statements! */
	}
	rcu_unregister_thread();
#ifdef DEBUG_TRACE
	trace_dump_thread(&tr_mine);
#endif /* #ifdef DEBUG_TRACE */
	wait_for_my_rcu_cbs(&cw);
	TREE_BUG_ON(cp->n_mallocs != cp->n_frees);
	atomic_inc(&nthreads_done);
	set_thread_call_rcu_data(NULL);
	call_rcu_data_free(crdp);
	return NULL;
}

static void tree_rcumalloc(void)
{
	struct rcumalloc_child *cp = malloc(sizeof(*cp) * nupdaters);
	int i;
	long long starttime;
	long long n_mallocs = 0LL;
	long long n_malloc_fails = 0LL;
	long long n_frees = 0LL;

	TREE_BUG_ON(cp == NULL);

	tracing_enable();

	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nupdaters; i++) {
		cp[i].me = i;
		cp[i].n_mallocs = 0LL;
		cp[i].n_malloc_fails = 0LL;
		cp[i].n_frees = 0LL;
		create_thread(tree_rcumalloc_child, &cp[i]);
	}

	/* Wait for all threads to initialize. */
	while (atomic_read(&nthreads_running) < nupdaters)
		poll(NULL, 0, 1);
	smp_mb();

	/* Run the test. */
	starttime = get_microseconds();
	ACCESS_ONCE(goflag) = GOFLAG_RUN;
	poll(NULL, 0, duration);
	ACCESS_ONCE(goflag) = GOFLAG_STOP;
	while (atomic_read(&nthreads_done) < nupdaters)
		poll(NULL, 0, 1);
	starttime = get_microseconds() - starttime;
	printf("Duration: %lld microseconds\n", starttime);
	wait_all_threads();

	/* Summarize results and output them. */
	for (i = 0; i < nupdaters; i++) {
		n_mallocs += cp[i].n_mallocs;
		n_malloc_fails += cp[i].n_malloc_fails;
		n_frees += cp[i].n_frees;
	}
	printf("mallocs: %lld %lld frees: %lld\n",
	       n_mallocs, n_malloc_fails, n_frees);
	free(cp);
	tracing_disable();
}

/* Common argument-parsing code. */
void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "Usage: %s --smoketest\n", progname);
	fprintf(stderr, "Usage: %s --stresstest\n", progname);
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds.\n");
	fprintf(stderr, "\t\tDefaults to 1000 (AKA one second).\n");
	fprintf(stderr, "\t--makegraph\n");
	fprintf(stderr, "\t\tOutput a graphviz .dot file showing tree.\n");
	fprintf(stderr, "\t\tDisabled by default.\n");
	fprintf(stderr, "\t--nel\n");
	fprintf(stderr, "\t\tNumber of tree elements, defaults to 512.\n");
	fprintf(stderr, "\t--nkeymult\n");
	fprintf(stderr, "\t\tSize of key space as a multiple of the\n");
	fprintf(stderr, "\t\tnumber of elements, defaults to 1.\n");
	fprintf(stderr, "\t--nupdaters\n");
	fprintf(stderr, "\t\tNumber of updaters, defaults to 1.\n");
	fprintf(stderr, "\t--every\n");
	fprintf(stderr, "\t\tOnly modulo-N keys, default modulo-2.\n");
	fprintf(stderr, "\t\tSet to zero to disable.\n");
	fprintf(stderr, "\t--one-to-one\n");
	fprintf(stderr, "\t\tUse consecutive keys.  This reduces\n");
	fprintf(stderr, "\t\tcontention, but also reduces code coverage.\n");
	fprintf(stderr, "\t--affinity\n");
	fprintf(stderr, "\t\tBind updaters to CPUs, using specified\n");
	fprintf(stderr, "\t\tstride.  Defaults to zero (don't affinity).\n");
	fprintf(stderr, "\t--tracerecs\n");
	fprintf(stderr, "\t\tNumber of trace records per thread.\n");
	fprintf(stderr, "\t--verbose\n");
	fprintf(stderr, "\t\tPrint more diagnostics, default disabled.\n");
	fprintf(stderr, "\t--lookupweight\n");
	fprintf(stderr, "\t\tLookup-operation weighting, defaults to 0.\n");
	fprintf(stderr, "\t--lookuprelaxweight\n");
	fprintf(stderr, "\t\tRelaxed lookup-operation weighting, defaults to 90.\n");
	fprintf(stderr, "\t--moveweight\n");
	fprintf(stderr, "\t\tMove-operation weighting, defaults to 0.\n");
	fprintf(stderr, "\t--scanweight\n");
	fprintf(stderr, "\t\tScan-operation weighting, defaults to 3.\n");
	fprintf(stderr, "\t--updateweight\n");
	fprintf(stderr, "\t\tUpdate-operation weighting, defaults to 7.\n");
	fprintf(stderr, "Usage: %s --rcumalloctest\n", progname);
	fprintf(stderr, "\tTakes --duration and --nupdaters as above.\n");
	exit(-1);
}

int main(int argc, char *argv[])
{
	struct cbs_wait cw;
	int i = 1;
	void (*test_to_do)(void) = NULL;

	smp_init();
	srandom(time(NULL));

	while (i < argc) {
		if (strcmp(argv[i], "--smoketest") == 0) {
			test_to_do = smoketest;
			if (i != 1)
				usage(argv[0],
				      "Excess arguments for %s\n", argv[i]);
		} else if (strcmp(argv[i], "--stresstest") == 0) {
			test_to_do = tree_stress_test;
			if (i != 1)
				usage(argv[0],
				      "Must be first argument: %s\n", argv[i]);
		} else if (strcmp(argv[i], "--rcumalloctest") == 0) {
			test_to_do = tree_rcumalloc;
			if (i != 1)
				usage(argv[0],
				      "Must be first argument: %s\n", argv[i]);
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = strtol(argv[++i], NULL, 0);
			if (duration < 0 || test_to_do == smoketest)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--makegraph") == 0) {
			makegraph = 1;
		} else if (strcmp(argv[i], "--nel") == 0) {
			nel = strtol(argv[++i], NULL, 0);
			if (nel <= 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nkeymult") == 0) {
			nkeymult = strtol(argv[++i], NULL, 0);
			if (nkeymult <= 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nupdaters") == 0) {
			nupdaters = strtol(argv[++i], NULL, 0);
			if (nupdaters < 1 && test_to_do != smoketest)
				usage(argv[0],
				      "%s must be >= 1\n", argv[i - 1]);
			if (nupdaters != 1 && test_to_do == smoketest)
				usage(argv[0],
				      "%s must equal 1 for --smoketest\n",
				      argv[i - 1]);
		} else if (strcmp(argv[i], "--every") == 0) {
			every = strtol(argv[++i], NULL, 0);
			if (every < 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--one-to-one") == 0) {
			one_to_one = 1;
		} else if (strcmp(argv[i], "--affinity") == 0) {
			affinity_step = strtol(argv[++i], NULL, 0);
			if (affinity_step < 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--tracerecs") == 0) {
			ntracerecs = strtol(argv[++i], NULL, 0);
			if (ntracerecs < 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
			if (ntracerecs)
				tracing_enable();
			else
				tracing_disable();
		} else if (strcmp(argv[i], "--verbose") == 0) {
			verbose = 1;
		} else if (strcmp(argv[i], "--lookupweight") == 0) {
			lookupweight = strtol(argv[++i], NULL, 0);
			if (lookupweight < 0 || lookupweight > 1000)
				usage(argv[0],
				      "Must have 1000 >= %s >= 0\n",
				      argv[i - 1]);
		} else if (strcmp(argv[i], "--lookuprelaxweight") == 0) {
			lookuprelaxweight = strtol(argv[++i], NULL, 0);
			if (lookuprelaxweight < 0 || lookuprelaxweight > 1000)
				usage(argv[0],
				      "Must have 1000 >= %s >= 0\n",
				      argv[i - 1]);
		} else if (strcmp(argv[i], "--moveweight") == 0) {
			moveweight = strtol(argv[++i], NULL, 0);
			if (moveweight < 0 || moveweight > 1000)
				usage(argv[0],
				      "Must have 1000 >= %s >= 0\n",
				      argv[i - 1]);
		} else if (strcmp(argv[i], "--scanweight") == 0) {
			scanweight = strtol(argv[++i], NULL, 0);
			if (scanweight < 0 || scanweight > 1000)
				usage(argv[0],
				      "Must have 1000 >= %s >= 0\n",
				      argv[i - 1]);
		} else if (strcmp(argv[i], "--updateweight") == 0) {
			updateweight = strtol(argv[++i], NULL, 0);
			if (updateweight < 0 || updateweight > 1000)
				usage(argv[0],
				      "Must have 1000 >= %s >= 0\n",
				      argv[i - 1]);
		} else {
			usage(argv[0], "Unrecognized: %s\n", argv[i]);
		}
		i++;
	};
	nkeys = nel * nkeymult;

	if (!test_to_do)
		usage(argv[0], "No test specified\n");
	test_to_do();

	wait_for_my_rcu_cbs(&cw);
	smp_mb();
	return 0;
}
