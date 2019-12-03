/*
 * skiplisttorture.h: simple user-level performance/stress test of skiplists.
 *
 * Usage:
 *
 *	./skiplist --smoketest
 *		Run a simple single-threaded smoke test.
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

#define _GNU_SOURCE
#include <unistd.h>
#include <stdlib.h>
#include <stdarg.h>
#include <sched.h>
#include <string.h>

/*
 * Test variables.
 */

struct testsl {
	struct skiplist sle_e;
	unsigned long data;
	struct rcu_head rh;
	int in_table __attribute__((__aligned__(CACHE_LINE_SIZE)));
};

void defer_del_done_stresstest(struct testsl *p)
{
	p->in_table = 0;
}

void *testgk(struct skiplist *slep)
{
	struct testsl *tslp;

	tslp = container_of(slep, struct testsl, sle_e);
	return (void *)tslp->data;
}

int testcmp(struct skiplist *slp, void *key)
{
	struct testsl *tslp;
	unsigned long a;
	unsigned long b;

	tslp = container_of(slp, struct testsl, sle_e);
	a = tslp->data;
	b = (unsigned long)key;
	return (a != b) - 2 * (a < b);
}

void sl_print(struct skiplist *slp)
{
	int i;
	struct testsl *tslp;

	if (slp == NULL) {
		printf("NULL\n");
		return;
	}
	tslp = container_of(slp, struct testsl, sle_e);
	printf("%p Key: %ld tl: %d %c%c\n\t",
	       tslp, (unsigned long)tslp->data, slp->sl_toplevel,
	       ".D"[!!slp->sl_deleted],
	       ".L"[!!spin_is_locked(&slp->sl_lock)]);
	for (i = 0; i < SL_MAX_LEVELS; i++)
		printf("%p ", slp->sl_next[i]);
	printf("\n");
}

void sl_dump(struct skiplist *head_slp)
{
	int i;
	char sep;
	struct skiplist *slp;
	struct testsl *tslp;

	if (head_slp == NULL) {
		printf("NULL\n");
		return;
	}
	for (slp = head_slp; slp != NULL; slp = slp->sl_next[0]) {
		tslp = container_of(slp, struct testsl, sle_e);
		printf("Key: %2ld (%p) tl: %c%c %d:",
		       (unsigned long)tslp->data, tslp,
		       ".D"[!!slp->sl_deleted],
		       ".L"[!!spin_is_locked(&slp->sl_lock)],
		       slp->sl_toplevel);
		for (i = 0; i < SL_MAX_LEVELS; i++) {
			if (slp->sl_next[i] == NULL)
				break;
			if (i == slp->sl_toplevel + 1)
				sep = '|';
			else
				sep = ' ';
			tslp = container_of(slp->sl_next[i],
					    struct testsl, sle_e);
			printf("%c%2ld", sep, (unsigned long)tslp->data);
		}
		for (; i < SL_MAX_LEVELS; i++)
			if (slp->sl_next[i] != NULL)
				printf(" !!!%d!!!", i);
		printf("\n");
	}
}

void update_dump(struct skiplist **update, int toplevel)
{
	int i;
	char sep;
	struct skiplist *slp;
	struct testsl *tslp;

	printf("update: tl=%d ", toplevel);
	for (i = 0; i <= toplevel; i++) {
		slp = update[i];
		if (slp == NULL)
			break;
		if (i == slp->sl_toplevel + 1)
			sep = '|';
		else
			sep = ' ';
		tslp = container_of(slp, struct testsl, sle_e);
		printf("%c%2ld", sep, (unsigned long)tslp->data);
	}
	for (; i < toplevel; i++)
		if (slp->sl_next[i] != NULL)
			printf(" !!!%d!!!", i);
	printf("\n");
}

void sl_print_next(struct skiplist *slp)
{
	int i;
	struct skiplist *slp_next = slp->sl_next[0];
	struct testsl *tslp;
	struct testsl *tslp_next;

	if (slp_next == NULL) {
		printf("%p -> NULL\n", slp);
		return;
	}
	tslp = container_of(slp, struct testsl, sle_e);
	tslp_next = container_of(slp_next, struct testsl, sle_e);
	printf("%p -> %p Key: %ld tl: %d %c%c\n\t",
	       tslp, tslp_next, (unsigned long)tslp_next->data,
	       slp_next->sl_toplevel,
	       ".D"[!!slp_next->sl_deleted],
	       ".L"[!!spin_is_locked(&slp_next->sl_lock)]);
	for (i = 0; i < SL_MAX_LEVELS; i++)
		printf("%p ", slp_next->sl_next[i]);
	printf("\n");
}

void testsl_insert(struct testsl *ep, struct testsl *ehp)
{
	int result;

	do {
		ep->data = random() % 9;
		result = skiplist_insert(&ep->sle_e, &ehp->sle_e,
					 (void *)ep->data);
	} while (result);
	skiplist_fsck(&ehp->sle_e);
}

void testsl_delete(struct testsl *ep, struct testsl *ehp)
{
	struct skiplist *slp;

	slp = skiplist_delete(&ehp->sle_e, (void *)ep->data);
	BUG_ON(slp != &ep->sle_e);
	skiplist_fsck(&ehp->sle_e);
}

void smoketest(void)
{
	static struct testsl e3 = { .sle_e.sl_toplevel = 0,
		.sle_e.sl_next = {       NULL,       NULL,       NULL, NULL },
		.data = 7 };
	static struct testsl e2 = { .sle_e.sl_toplevel = 0,
		.sle_e.sl_next = {  &e3.sle_e,       NULL,       NULL, NULL },
		.data = 5 };
	static struct testsl e1 = { .sle_e.sl_toplevel = 1,
		.sle_e.sl_next = {  &e2.sle_e,       NULL,       NULL, NULL },
		.data = 3 };
	static struct testsl e0 = { .sle_e.sl_toplevel = 0,
		.sle_e.sl_next = {  &e1.sle_e,       NULL,       NULL, NULL },
		.data = 1 };
	static struct testsl eh = { .sle_e.sl_toplevel = SL_MAX_LEVELS - 1,
		.sle_e.sl_cmp = testcmp,
		.sle_e.sl_next = {  &e0.sle_e,  &e1.sle_e,       NULL, NULL } };
	static struct testsl e00; /* Initialized at insertion time. */
	long i;
	int result;
	struct skiplist_iter sli;
	struct skiplist *slp;
	struct skiplist *slp_prev;
	int toplevel;
	struct skiplist *update[SL_MAX_LEVELS];

	spin_lock_init(&eh.sle_e.sl_lock);
	spin_lock_init(&e0.sle_e.sl_lock);
	spin_lock_init(&e1.sle_e.sl_lock);
	spin_lock_init(&e2.sle_e.sl_lock);
	spin_lock_init(&e3.sle_e.sl_lock);
	eh.sle_e.sl_head = &eh.sle_e;
	e0.sle_e.sl_head = &eh.sle_e;
	e1.sle_e.sl_head = &eh.sle_e;
	e2.sle_e.sl_head = &eh.sle_e;
	e3.sle_e.sl_head = &eh.sle_e;

	rcu_register_thread();

	rcu_read_lock();

	skiplist_fsck(&eh.sle_e);

	printf("\nskiplist_lookup_help():\n");
	for (i = 0; i <= 8; i++) {
		slp = skiplist_lookup_help(&eh.sle_e, (void *)i);
		printf("%ld: ", i);
		sl_print_next(slp);
		skiplist_fsck(&eh.sle_e);
	}

	printf("\nskiplist_lookup_relaxed():\n");
	for (i = 0; i <= 8; i++) {
		slp = skiplist_lookup_relaxed(&eh.sle_e, (void *)i);
		printf("%ld: ", i);
		sl_print(slp);
		skiplist_fsck(&eh.sle_e);
	}

	printf("\nskiplist_lookup_lock_prev():\n");
	for (i = 0; i <= 8; i++) {
		slp = skiplist_lookup_lock_prev(&eh.sle_e, (void *)i,
						&slp_prev, &result);
		printf("---\n");
		printf("%ld%c ", i, "<:>"[result + 1]);
		sl_print(slp_prev);
		skiplist_fsck(&eh.sle_e);
		printf("%ld. ", i);
		sl_print_next(slp_prev);
		if (slp) {
			skiplist_unlock(slp_prev);
			skiplist_fsck(&eh.sle_e);
		}
	}

	printf("\nskiplist_lookup_lock():\n");
	for (i = 0; i <= 8; i++) {
		slp = skiplist_lookup_lock(&eh.sle_e, (void *)i);
		printf("%ld: ", i);
		sl_print(slp);
		skiplist_fsck(&eh.sle_e);
		if (slp) {
			skiplist_unlock(slp);
			skiplist_fsck(&eh.sle_e);
		}
	}

	printf("\n");
	for (i = 0; i <= 8; i++) {
		printf("---\nskiplist_insert_lock(%ld):\n", i);
		toplevel = skiplist_insert_lock(&eh.sle_e, (void *)i, update);
		if (toplevel < 0)
			break;
		update_dump(update, toplevel);
		sl_dump(&eh.sle_e);
		skiplist_fsck(&eh.sle_e);
		if (toplevel >= 0) {
			printf("skiplist_unlock_update():\n");
			skiplist_unlock_update(update, toplevel);
			sl_dump(&eh.sle_e);
			skiplist_fsck(&eh.sle_e);
		}
	}

	for (i = 0; i < 10; i++) {
		e00.data = random() % 9;
		printf("\nskiplist_insert(%lu)\n", e00.data);
		result = skiplist_insert(&e00.sle_e, &eh.sle_e,
					 (void *)e00.data);
		printf("%lu insertion: %s\n", e00.data,
		       result == 0
			? "Successful"
			: result == -EEXIST ? "Already present" : "Failed");
		sl_dump(&eh.sle_e);
		skiplist_fsck(&eh.sle_e);
		if (result == 0) {
			printf("\nskiplist_delete()\n");
			slp = skiplist_delete(&eh.sle_e, (void *)e00.data);
			BUG_ON(slp != &e00.sle_e);
			sl_dump(&eh.sle_e);
			skiplist_fsck(&eh.sle_e);
		}
	}

	printf("\nValue iterators:\n");
	slp = skiplist_valiter_first(&eh.sle_e);
	assert(slp == &e0.sle_e);
	printf("\tskiplist_valiter_first() OK.\n");
	slp = skiplist_valiter_next(&eh.sle_e, (void *)e0.data);
	assert(slp == &e1.sle_e);
	printf("\tskiplist_valiter_next(e0) OK.\n");
	slp = skiplist_valiter_next(&eh.sle_e, (void *)e1.data);
	assert(slp == &e2.sle_e);
	printf("\tskiplist_valiter_next(e1) OK.\n");
	slp = skiplist_valiter_next(&eh.sle_e, (void *)e2.data);
	assert(slp == &e3.sle_e);
	printf("\tskiplist_valiter_next(e2) OK.\n");
	slp = skiplist_valiter_next(&eh.sle_e, (void *)e3.data);
	assert(slp == NULL);
	printf("\tskiplist_valiter_next(e3) OK (NULL).\n");

	slp = skiplist_valiter_last(&eh.sle_e);
	assert(slp == &e3.sle_e);
	printf("\n\tskiplist_valiter_last() OK.\n");
	slp = skiplist_valiter_prev(&eh.sle_e, (void *)e3.data);
	assert(slp == &e2.sle_e);
	printf("\tskiplist_valiter_prev(e3) OK.\n");
	slp = skiplist_valiter_prev(&eh.sle_e, (void *)e2.data);
	assert(slp == &e1.sle_e);
	printf("\tskiplist_valiter_prev(e2) OK.\n");
	slp = skiplist_valiter_prev(&eh.sle_e, (void *)e1.data);
	assert(slp == &e0.sle_e);
	printf("\tskiplist_valiter_prev(e1) OK.\n");
	slp = skiplist_valiter_prev(&eh.sle_e, (void *)e0.data);
	assert(slp == NULL);
	printf("\tskiplist_valiter_prev(e0) OK (NULL).\n");

	printf("\nPointer-hinted iterators:\n");
	slp = skiplist_ptriter_first(&eh.sle_e, &sli);
	assert(slp == &e0.sle_e);
	printf("\tskiplist_ptriter_first() OK.\n");
	slp = skiplist_ptriter_next(&eh.sle_e, (void *)e0.data, &sli);
	assert(slp == &e1.sle_e);
	printf("\tskiplist_ptriter_next(e0) OK.\n");
	printf("\tInsert and then delete an element to invalidate hint.\n");
	e00.data = 10;
	result = skiplist_insert(&e00.sle_e, &eh.sle_e, (void *)e00.data);
	BUG_ON(result);
	slp = skiplist_delete(&eh.sle_e, (void *)e00.data);
	BUG_ON(slp != &e00.sle_e);
	slp = skiplist_ptriter_next(&eh.sle_e, (void *)e1.data, &sli);
	assert(slp == &e2.sle_e);
	printf("\tskiplist_ptriter_next(e1) OK.\n");
	slp = skiplist_ptriter_next(&eh.sle_e, (void *)e2.data, &sli);
	assert(slp == &e3.sle_e);
	printf("\tskiplist_ptriter_next(e2) OK.\n");
	slp = skiplist_ptriter_next(&eh.sle_e, (void *)e3.data, &sli);
	assert(slp == NULL);
	printf("\tskiplist_ptriter_next(e3) OK (NULL).\n");

	slp = skiplist_ptriter_last(&eh.sle_e, &sli);
	assert(slp == &e3.sle_e);
	printf("\n\tskiplist_ptriter_last() OK.\n");
	slp = skiplist_ptriter_prev(&eh.sle_e, (void *)e3.data, &sli);
	assert(slp == &e2.sle_e);
	printf("\tskiplist_ptriter_prev(e3) OK.\n");
	slp = skiplist_ptriter_prev(&eh.sle_e, (void *)e2.data, &sli);
	assert(slp == &e1.sle_e);
	printf("\tskiplist_ptriter_prev(e2) OK.\n");
	slp = skiplist_ptriter_prev(&eh.sle_e, (void *)e1.data, &sli);
	assert(slp == &e0.sle_e);
	printf("\tskiplist_ptriter_prev(e1) OK.\n");
	slp = skiplist_ptriter_prev(&eh.sle_e, (void *)e0.data, &sli);
	assert(slp == NULL);
	printf("\tskiplist_ptriter_prev(e0) OK (NULL).\n");

	printf("\nsl_dump():\n");
	sl_dump(&eh.sle_e);

	printf("\nRebalancing:\n");
	skiplist_init(&eh.sle_e, testcmp);
	e0.data = 1;
	testsl_insert(&e0, &eh);
	e1.data = 2;
	testsl_insert(&e1, &eh);
	e2.data = 3;
	testsl_insert(&e2, &eh);
	e3.data = 4;
	testsl_insert(&e3, &eh);
	e00.data = 5;
	testsl_insert(&e00, &eh);
	sl_dump(&eh.sle_e);
	printf("--- Node 0 to level 7:\n");
	skiplist_balance_node(&eh.sle_e, (void *)0, 7);
	sl_dump(&eh.sle_e);
	printf("--- Node 1 to level 6:\n");
	skiplist_balance_node(&eh.sle_e, (void *)1, 6);
	sl_dump(&eh.sle_e);

	printf("\nRandom insertions:\n");
	for (i = 0; i < 100000; i++) {
		skiplist_init(&eh.sle_e, testcmp);
		e0.data = random() % 9;
		testsl_insert(&e0, &eh);
		e1.data = random() % 9;
		testsl_insert(&e1, &eh);
		e2.data = random() % 9;
		testsl_insert(&e2, &eh);
		e3.data = random() % 9;
		testsl_insert(&e3, &eh);
		e00.data = random() % 9;
		testsl_insert(&e00, &eh);

		testsl_delete(&e0, &eh);
		testsl_delete(&e1, &eh);
		testsl_delete(&e2, &eh);
		testsl_delete(&e3, &eh);
		testsl_delete(&e00, &eh);
	}

	rcu_read_unlock();

	rcu_unregister_thread();
	printf("End of smoketest.\n");
}


/* Parameters for performance test. */
int dump_skiplists = 0;
int no_bal = 0;
int no_scan = 0;
int nreaders = 2;
int nupdaters = 5;
int updatewait = 1;
long elperupdater = 2048; /* Allow for them being stuck in grace periods. */
long valsperupdater = 32;
int cpustride = 1;
long duration = 10; /* in milliseconds. */
static int debug = 0;

atomic_t nthreads_running;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

/* Per-test-thread attribute/statistics structure. */
struct stresstest_attr {
	int myid;
	long long nlookups;
	long long nlookupfails;
	long long nscans;
	long long nadds;
	long long naddfails;
	long long nbals;
	long long ndels;
	long long ndelfails;
	int mycpu;
	long nelements;
	int cat;
};

void (*defer_del_done)(struct testsl *) = NULL;

void defer_del_rcu(struct rcu_head *rhp)
{
	struct testsl *tslp;

	tslp = container_of(rhp, struct testsl, rh);
	defer_del_done(tslp);
}

struct testsl head_sl;

/* Look up a key in the skiplist. */
int stresstest_lookup(long i)
{
	struct skiplist *slp;
	struct testsl *tslp;

	slp = skiplist_lookup_relaxed(&head_sl.sle_e, (void *)i);
	tslp = container_of(slp, struct testsl, sle_e);
	BUG_ON(slp && tslp->data != i);
	BUG_ON(slp && !tslp->in_table);
	return !!slp;
}

/* Add an element to the skiplist. */
int stresstest_add(struct testsl *tslp)
{
	int result;

	BUG_ON(tslp->in_table);
	tslp->in_table = 1;
	result = skiplist_insert(&tslp->sle_e, &head_sl.sle_e,
				 (void *)tslp->data);
	if (result)
		tslp->in_table = 0;
	return result;
}

/* Remove an element from the skiplist. */
int stresstest_del(unsigned long key)
{
	struct skiplist *slp;
	struct testsl *tslp;

	slp = skiplist_delete(&head_sl.sle_e, (void *)key);
	if (!slp)
		return -ENOENT;
	tslp = container_of(slp, struct testsl, sle_e);
	tslp->in_table = 2;
	defer_del(&tslp->rh);
	return 0;
}

/* Do a forward and a reverse scan of the entire skiplist. */
int stresstest_reader_scan(void)
{
	struct skiplist_iter sli;
	struct skiplist *slp;
	struct testsl *tslp;

	/* Value-based iterators. */
	rcu_read_lock();
	slp = skiplist_valiter_first(&head_sl.sle_e);
	while (slp) {
		rcu_read_unlock();
		tslp = container_of(slp, struct testsl, sle_e);
		slp = skiplist_valiter_next(&head_sl.sle_e,
					    (void *)tslp->data);
		rcu_read_lock();
	}
	slp = skiplist_valiter_last(&head_sl.sle_e);
	while (slp) {
		rcu_read_unlock();
		tslp = container_of(slp, struct testsl, sle_e);
		slp = skiplist_valiter_prev(&head_sl.sle_e,
					    (void *)tslp->data);
		rcu_read_lock();
	}
	rcu_read_unlock();

	/* Pointer-hint-based iterators. */
	rcu_read_lock();
	slp = skiplist_ptriter_first(&head_sl.sle_e, &sli);
	while (slp) {
		rcu_read_unlock();
		tslp = container_of(slp, struct testsl, sle_e);
		slp = skiplist_ptriter_next(&head_sl.sle_e,
					    (void *)tslp->data, &sli);
		rcu_read_lock();
	}
	slp = skiplist_ptriter_last(&head_sl.sle_e, &sli);
	while (slp) {
		rcu_read_unlock();
		tslp = container_of(slp, struct testsl, sle_e);
		slp = skiplist_ptriter_prev(&head_sl.sle_e,
					    (void *)tslp->data, &sli);
		rcu_read_lock();
	}
	rcu_read_unlock();

	return 4;
}

/* Stress test reader thread. */
void *stresstest_reader(void *arg)
{
	int gf;
	long i;
	struct stresstest_attr *pap = arg;
	long long nlookups = 0;
	long long nlookupfails = 0;
	long long nscans = 0;

	run_on(pap->mycpu);
	rcu_register_thread();

	/* Warm up cache. */
	for (i = 0; i < valsperupdater * nupdaters; i++) {
		stresstest_lookup(i);
	}

	/* Record our presence. */
	atomic_inc(&nthreads_running);

	/* Run the test code. */
	i = 0;
	for (;;) {
		gf = ACCESS_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nlookups = 0;
				nlookupfails = 0;
				nscans = 0;
			}
		}
		rcu_read_lock();
		if (!stresstest_lookup(i))
			nlookupfails++;
		rcu_read_unlock();
		nlookups++;
		i++;
		if (i >= valsperupdater * nupdaters)
			i = 0;
		if (!no_scan)
			nscans += stresstest_reader_scan();
	}
	pap->nlookups = nlookups;
	pap->nlookupfails = nlookupfails;
	pap->nscans = nscans;
	rcu_unregister_thread();
	return NULL;
}

/* Stress test updater thread. */
void *stresstest_updater(void *arg)
{
	long i;
	long j;
	long k;
	void *key;
	int gf;
	struct stresstest_attr *pap = arg;
	int myid = pap->myid;
	int mylowkey = myid * elperupdater;
	struct testsl *tslp;
	long long nadds = 0;
	long long naddfails = 0;
	long long nbals = 0;
	long long ndels = 0;
	long long ndelfails = 0;

	tslp = malloc(sizeof(*tslp) * elperupdater);
	BUG_ON(tslp == NULL);
	for (i = 0; i < elperupdater; i++) {
		tslp[i].data = i % valsperupdater + mylowkey;
		tslp[i].in_table = 0;
	}
	run_on(pap->mycpu);
	rcu_register_thread();

	/* Start with some random half of the elements in the hash table. */
	for (i = 0; i < elperupdater / 2; i++) {
		j = random() % elperupdater;
		while (tslp[j].in_table)
			if (++j >= elperupdater)
				j = 0;
		stresstest_add(&tslp[j]);
	}

	/* Announce our presence and enter the test loop. */
	atomic_inc(&nthreads_running);
	i = 0;
	j = 0;
	for (;;) {
		gf = ACCESS_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nadds = 0;
				naddfails = 0;
				nbals = 0;
				ndels = 0;
				ndelfails = 0;
			}
		}
		if (updatewait == 0) {
			poll(NULL, 0, 10);  /* No actual updating wanted. */
		} else {
			while (tslp[i].in_table) {
				if (++i >= elperupdater) {
					i = 0;
					break;
				}
			}
			if (tslp[i].in_table == 0) {
				nadds++;
				if (stresstest_add(&tslp[i]))
					naddfails++;
				if ((nadds & 0xff) == 0)
					quiescent_state();
				if ((nadds & 0xff) == 0 && !no_bal) {
					k = random() % SL_MAX_LEVELS;
					key = (void *)tslp[i].data;
					skiplist_balance_node(&head_sl.sle_e,
							      key, k);
					nbals++;
				}
			}
			ndels++;
			if (stresstest_del((unsigned long)j))
				ndelfails++;
			if (++j >= valsperupdater * nupdaters)
				j = 0;
		}

		/* Add requested delay. */
		if (updatewait < 0) {
			poll(NULL, 0, -updatewait);
		} else {
			for (k = 0; k < updatewait; k++)
				barrier();
		}
	}

	/* Test over, so remove all our elements from the hash table. */
	for (i = 0; i < elperupdater; i++) {
		if (tslp[i].in_table != 1)
			continue;
		(void)stresstest_del(tslp[i].data);
	}

	skiplist_lock(&head_sl.sle_e);
	if (dump_skiplists) {
		printf("Skiplist dump 2 from thread %d\n:", pap->myid);
		sl_dump(&head_sl.sle_e);
		fflush(stdout);
	}
	skiplist_fsck(&head_sl.sle_e);
	skiplist_unlock(&head_sl.sle_e);

	/* Really want rcu_barrier(), but missing from old liburcu versions. */
	synchronize_rcu();
	poll(NULL, 0, 100);
	synchronize_rcu();

	skiplist_lock(&head_sl.sle_e);
	if (dump_skiplists) {
		printf("Skiplist dump 2 from thread %d\n:", pap->myid);
		sl_dump(&head_sl.sle_e);
		fflush(stdout);
	}
	skiplist_fsck(&head_sl.sle_e);
	skiplist_unlock(&head_sl.sle_e);

	rcu_unregister_thread();
	free(tslp);
	pap->nadds = nadds;
	pap->naddfails = naddfails;
	pap->nbals = nbals;
	pap->ndels = ndels;
	pap->ndelfails = ndelfails;
	return NULL;
}

/* Run a performance test. */
void stresstest(void)
{
	struct stresstest_attr *pap;
	int maxcpus = sysconf(_SC_NPROCESSORS_CONF);
	long i;
	long long nlookups = 0;
	long long nlookupfails = 0;
	long long nscans = 0;
	long long nadds = 0;
	long long naddfails = 0;
	long long nbals = 0;
	long long ndels = 0;
	long long ndelfails = 0;
	long long starttime;
	long long endtime;

	BUG_ON(maxcpus <= 0);
	rcu_register_thread();
	skiplist_init(&head_sl.sle_e, testcmp);
	defer_del_done = defer_del_done_stresstest;
	pap = malloc(sizeof(*pap) * (nreaders + nupdaters));
	BUG_ON(pap == NULL);
	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nreaders + nupdaters; i++) {
		pap[i].myid = i < nreaders ? i : i - nreaders;
		pap[i].nlookups = 0;
		pap[i].nlookupfails = 0;
		pap[i].nscans = 0;
		pap[i].nadds = 0;
		pap[i].naddfails = 0;
		pap[i].nbals = 0;
		pap[i].ndels = 0;
		pap[i].ndelfails = 0;
		pap[i].mycpu = (i * cpustride) % maxcpus;
		pap[i].nelements = nupdaters * elperupdater;
		create_thread(i < nreaders
					? stresstest_reader
					: stresstest_updater,
			      &pap[i]);
	}

	/* Wait for all threads to initialize. */
	while (atomic_read(&nthreads_running) < nreaders + nupdaters)
		poll(NULL, 0, 1);
	smp_mb();

	/* Run the test. */
	starttime = get_microseconds();
	ACCESS_ONCE(goflag) = GOFLAG_RUN;
	do {
		poll(NULL, 0, duration);
		endtime = get_microseconds();
	} while (endtime - starttime < duration * 1000);
	starttime = endtime - starttime;
	ACCESS_ONCE(goflag) = GOFLAG_STOP;
	wait_all_threads();

	/* Don't need to lock anything here: No more updates happening. */
	if (dump_skiplists) {
		printf("Skiplist dump from parent thread\n:");
		sl_dump(&head_sl.sle_e);
		fflush(stdout);
	}
	skiplist_fsck(&head_sl.sle_e);

	/* Collect stats and output them. */
	for (i = 0; i < nreaders + nupdaters; i++) {
		nlookups += pap[i].nlookups;
		nlookupfails += pap[i].nlookupfails;
		nscans += pap[i].nscans;
		nadds += pap[i].nadds;
		naddfails += pap[i].naddfails;
		nbals += pap[i].nbals;
		ndels += pap[i].ndels;
		ndelfails += pap[i].ndelfails;
	}
	printf("nlookups: %lld %lld scans: %lld  nadds: %lld %lld  nbals: %lld  ndels: %lld %lld  duration: %g\n",
	       nlookups, nlookupfails, nscans, nadds, naddfails, nbals, ndels, ndelfails, starttime / 1000.);
	printf("ns/read+scan: %g  ns/update: %g\n",
	       (starttime * 1000. * (double)nreaders) / (double)(nlookups + nscans),
	       ((starttime * 1000. * (double)nupdaters) /
	        (double)(nadds + ndels)));

	free(pap);
	rcu_unregister_thread();
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
	fprintf(stderr, "\t--cpustride\n");
	fprintf(stderr, "\t\tCPU stride, defaults to 1.\n");
	fprintf(stderr, "\t--debug\n");
	fprintf(stderr, "\t\tEnable additional debug checks.\n");
	fprintf(stderr, "\t--dump_skiplists\n");
	fprintf(stderr, "\t\tDump skiplists at end of stresstest.\n");
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds, defaults.\n");
	fprintf(stderr, "\t\tto 10.\n");
	fprintf(stderr, "\t--elperupdater\n");
	fprintf(stderr, "\t\tSkiplist elements per updater.  A largish\n");
	fprintf(stderr, "\t\tnumber is required to allow for grace-period\n");
	fprintf(stderr, "\t\tlatency.  Defaults to 2048.\n");
	fprintf(stderr, "\t--no-bal\n");
	fprintf(stderr, "\t\tOmit skiplist balances from stresstest.\n");
	fprintf(stderr, "\t--no-scan\n");
	fprintf(stderr, "\t\tOmit full-skiplist scans from stresstest.\n");
	fprintf(stderr, "\t--nreaders\n");
	fprintf(stderr, "\t\tNumber of reader threads.\n");
	fprintf(stderr, "\t--nupdaters\n");
	fprintf(stderr, "\t\tNumber of updater threads.\n");
	fprintf(stderr, "\t--updatewait\n");
	fprintf(stderr, "\t\tNumber of spin-loop passes per update,\n");
	fprintf(stderr, "\t\tdefaults to -1.  If 0, the updater will not.\n");
	fprintf(stderr, "\t\tdo any updates, except for initialization.\n");
	fprintf(stderr, "\t\tIf negative, the updater waits for the\n");
	fprintf(stderr, "\t\tcorresponding number of milliseconds\n");
	fprintf(stderr, "\t\tbetween updates.\n");
	fprintf(stderr, "\t--valsperupdater\n");
	fprintf(stderr, "\t\tSkiplist key values per updater.  This should\n");
	fprintf(stderr, "\t\tbe about two orders of magnitude less than the\n");
	fprintf(stderr, "\t\tvalue for elsperupdater, defaults to 2048.\n");
	exit(-1);
}

int main(int argc, char *argv[])
{
	int i = 1;
	void (*test_to_do)(void) = NULL;

	smp_init();
	srandom(time(NULL));

	while (i < argc) {
		if (strcmp(argv[i], "--smoketest") == 0) {
			if (i < argc - 1 || i != 1)
				usage(argv[0],
				      "Excess arguments for %s\n", argv[i]);
			smoketest();
			exit(0);

		} else if (strcmp(argv[i], "--stresstest") == 0) {
			test_to_do = stresstest;
			if (i != 1)
				usage(argv[0],
				      "Must be first argument: %s\n", argv[i]);
		} else if (strcmp(argv[i], "--cpustride") == 0) {
			cpustride = strtol(argv[++i], NULL, 0);
			if (cpustride <= 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--debug") == 0) {
			debug = 1;
		} else if (strcmp(argv[i], "--dump-skiplists") == 0) {
			dump_skiplists = 1;
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = strtol(argv[++i], NULL, 0);
			if (duration < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--elperupdater") == 0) {
			elperupdater = strtol(argv[++i], NULL, 0);
			if (elperupdater <= 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--no-bal") == 0) {
			no_bal = 1;
		} else if (strcmp(argv[i], "--no-scan") == 0) {
			no_scan = 1;
		} else if (strcmp(argv[i], "--nreaders") == 0) {
			nreaders = strtol(argv[++i], NULL, 0);
			if (nreaders < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nupdaters") == 0) {
			nupdaters = strtol(argv[++i], NULL, 0);
			if (nupdaters < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--updatewait") == 0) {
			updatewait = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--valsperupdater") == 0) {
			valsperupdater = strtol(argv[++i], NULL, 0);
			if (valsperupdater <= 0)
				usage(argv[0],
				      "%s must be > 0\n", argv[i - 1]);
		} else {
			usage(argv[0], "Unrecognized argument: %s\n",
			      argv[i]);
		}
		i++;
	}
	if (!test_to_do)
		usage(argv[0], "No test specified\n");
	test_to_do();
	return 0;
}
