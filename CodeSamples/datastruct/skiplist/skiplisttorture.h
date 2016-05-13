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
 * Copyright (c) 2016 Paul E. McKenney, IBM Corporation.
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
	int held;
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
					 (void *)ep->data, testcmp);
	} while (result);
	skiplist_fsck(&ehp->sle_e, testcmp);
}

void testsl_delete(struct testsl *ep, struct testsl *ehp)
{
	struct skiplist *slp;

	slp = skiplist_delete(&ehp->sle_e, (void *)ep->data, testcmp);
	BUG_ON(slp != &ep->sle_e);
	skiplist_fsck(&ehp->sle_e, testcmp);
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
		.sle_e.sl_next = {  &e0.sle_e,  &e1.sle_e,       NULL, NULL } };
	static struct testsl e00; /* Initialized at insertion time. */
	long i;
	int result;
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

	skiplist_fsck(&eh.sle_e, testcmp);

	printf("\nskiplist_lookup_help():\n");
	for (i = 0; i <= 8; i++) {
		slp = skiplist_lookup_help(&eh.sle_e, (void *)i, testcmp);
		printf("%ld: ", i);
		sl_print_next(slp);
		skiplist_fsck(&eh.sle_e, testcmp);
	}

	printf("\nskiplist_lookup_relaxed():\n");
	for (i = 0; i <= 8; i++) {
		slp = skiplist_lookup_relaxed(&eh.sle_e, (void *)i, testcmp);
		printf("%ld: ", i);
		sl_print(slp);
		skiplist_fsck(&eh.sle_e, testcmp);
	}

	printf("\nskiplist_lookup_lock_prev():\n");
	for (i = 0; i <= 8; i++) {
		slp = skiplist_lookup_lock_prev(&eh.sle_e, (void *)i, testcmp,
						&slp_prev, &result);
		printf("---\n");
		printf("%ld%c ", i, "<:>"[result + 1]);
		sl_print(slp_prev);
		skiplist_fsck(&eh.sle_e, testcmp);
		printf("%ld. ", i);
		sl_print_next(slp_prev);
		skiplist_unlock(slp_prev);
		skiplist_fsck(&eh.sle_e, testcmp);
	}

	printf("\nskiplist_lookup_lock():\n");
	for (i = 0; i <= 8; i++) {
		slp = skiplist_lookup_lock(&eh.sle_e, (void *)i, testcmp);
		printf("%ld: ", i);
		sl_print(slp);
		skiplist_fsck(&eh.sle_e, testcmp);
		if (slp) {
			skiplist_unlock(slp);
			skiplist_fsck(&eh.sle_e, testcmp);
		}
	}

	printf("\n");
	for (i = 0; i <= 8; i++) {
		printf("---\nskiplist_insert_lock(%ld):\n", i);
		toplevel = skiplist_insert_lock(&eh.sle_e, (void *)i, testcmp,
						update);
		if (toplevel < 0)
			break;
		update_dump(update, toplevel);
		sl_dump(&eh.sle_e);
		skiplist_fsck(&eh.sle_e, testcmp);
		if (toplevel >= 0) {
			printf("skiplist_unlock_update():\n");
			skiplist_unlock_update(update, toplevel);
			sl_dump(&eh.sle_e);
			skiplist_fsck(&eh.sle_e, testcmp);
		}
	}

	for (i = 0; i < 10; i++) {
		e00.data = random() % 9;
		printf("\nskiplist_insert(%lu)\n", e00.data);
		result = skiplist_insert(&e00.sle_e, &eh.sle_e,
					 (void *)e00.data, testcmp);
		printf("%lu insertion: %s\n", e00.data,
		       result == 0
			? "Successful"
			: result == -EEXIST ? "Already present" : "Failed");
		sl_dump(&eh.sle_e);
		skiplist_fsck(&eh.sle_e, testcmp);
		if (result == 0) {
			printf("\nskiplist_delete()\n");
			slp = skiplist_delete(&eh.sle_e, (void *)e00.data,
					      testcmp);
			BUG_ON(slp != &e00.sle_e);
			sl_dump(&eh.sle_e);
			skiplist_fsck(&eh.sle_e, testcmp);
		}
	}

	printf("\nsl_dump():\n");
	sl_dump(&eh.sle_e);

	printf("\nRandom insertions:\n");
	for (i = 0; i < 100000; i++) {
		skiplist_init(&eh.sle_e);
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

#if 0

/* Parameters for performance test. */
int nbuckets = 1024;
int nreaders = 1;
int ncats = 0;
int nupdaters = 1;
int updatewait = -1;
long elperupdater = 2048;
int cpustride = 1;
int resizediv = 0;
int resizemult = 0;
int resizewait = 1;
long long nresizes = 0;
long duration = 10; /* in milliseconds. */

atomic_t nthreads_running;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

/* Per-test-thread attribute/statistics structure. */
struct perftest_attr {
	int myid;
	long long nlookups;
	long long nlookupfails;
	long long nadds;
	long long ndels;
	int mycpu;
	long nelements;
	int cat;
};

struct hashtab *perftest_htp = NULL;

/* Repeatedly resize a hash table. */
void *perftest_resize(void *arg)
{
	long els[2];
	int i = 0;

	hash_register_thread();
	run_on(0);
	els[0]= nbuckets;
	els[1] = els[0] * resizemult / resizediv;
	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (goflag == GOFLAG_RUN) {
		smp_mb();
		if (resizewait != 0)
			poll(NULL, 0, resizewait);
		i++;
		hash_resize_test(perftest_htp, els[i & 0x1]);
	}
	nresizes = i;
	hash_unregister_thread();
	return NULL;
}

/* Look up a key in the hash table. */
int perftest_lookup(long i)
{
	struct skiplist *slp;
	struct testsl *tslp;

	hashtab_lock_lookup(perftest_htp, i);
	slp = hashtab_lookup(perftest_htp, i, (void *)i, testcmp);
	tslp = container_of(slp, struct testsl, sle_e);
	BUG_ON(tslp && tslp->data != i);
	hashtab_unlock_lookup(perftest_htp, i);
	return !!slp;
}

/* Add an element to the hash table. */
void perftest_add(struct testsl *tslp)
{
	BUG_ON(tslp->in_table);
	hashtab_lock_mod(perftest_htp, tslp->data);
	BUG_ON(hashtab_lookup(perftest_htp, tslp->data,
			      (void *)tslp->data, testcmp));
	tslp->in_table = 1;
	hashtab_add(perftest_htp, tslp->data, &tslp->sle_e);
	hashtab_unlock_mod(perftest_htp, tslp->data);
}

/* Remove an element from the hash table. */
void perftest_del(struct testsl *tslp)
{
	BUG_ON(tslp->in_table != 1);
	hashtab_lock_mod(perftest_htp, tslp->data);
	hashtab_del(&tslp->sle_e);
	tslp->in_table = 2;
	hashtab_unlock_mod(perftest_htp, tslp->data);
	defer_del(&tslp->rh);
}

/* Performance test reader thread. */
void *perftest_reader(void *arg)
{
	int gf;
	long i;
	struct perftest_attr *pap = arg;
	long mydelta = primes[pap->myid]; /* Force different reader paths. */
	long ne = pap->nelements;
	int offset = (ne / mydelta) * mydelta == ne;
	long long nlookups = 0;
	long long nlookupfails = 0;

	run_on(pap->mycpu);
	hash_register_thread();

	/* Warm up cache. */
	for (i = 0; i < ne; i++)
		perftest_lookup(i);

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
			}
		}
		if (!perftest_lookup(i))
			nlookupfails++;
		nlookups++;
		i += mydelta;
		if (i >= ne)
			i = i % ne + offset;
	}
	pap->nlookups = nlookups;
	pap->nlookupfails = nlookupfails;
	hash_unregister_thread();
	return NULL;
}

/* Performance test updater thread. */
void *perftest_updater(void *arg)
{
	long i;
	long j;
	int gf;
	struct perftest_attr *pap = arg;
	int myid = pap->myid;
	int mylowkey = myid * elperupdater;
	struct testsl *tslp;
	long long nadds = 0;
	long long ndels = 0;

	tslp = malloc(sizeof(*tslp) * elperupdater);
	BUG_ON(tslp == NULL);
	for (i = 0; i < elperupdater; i++) {
		tslp[i].data = i + mylowkey;
		tslp[i].in_table = 0;
	}
	run_on(pap->mycpu);
	hash_register_thread();

	/* Start with some random half of the elements in the hash table. */
	for (i = 0; i < elperupdater / 2; i++) {
		j = random() % elperupdater;
		while (tslp[j].in_table)
			if (++j >= elperupdater)
				j = 0;
		perftest_add(&tslp[j]);
	}

	/* Announce our presence and enter the test loop. */
	atomic_inc(&nthreads_running);
	i = 0;
	for (;;) {
		gf = ACCESS_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nadds = 0;
				ndels = 0;
			}
		}
		if (updatewait == 0) {
			poll(NULL, 0, 10);  /* No actual updating wanted. */
		} else if (tslp[i].in_table == 1) {
			perftest_del(&tslp[i]);
			ndels++;
		} else if (tslp[i].in_table == 0) {
			perftest_add(&tslp[i]);
			nadds++;
		}

		/* Add requested delay. */
		if (updatewait < 0) {
			poll(NULL, 0, -updatewait);
		} else {
			for (j = 0; j < updatewait; j++)
				barrier();
		}
		if (++i >= elperupdater)
			i = 0;
		if ((i & 0xf) == 0)
			quiescent_state();
	}

	/* Test over, so remove all our elements from the hash table. */
	for (i = 0; i < elperupdater; i++) {
		if (tslp[i].in_table != 1)
			continue;
		BUG_ON(!perftest_lookup(tslp[i].data));
		perftest_del(&tslp[i]);
	}
	/* Really want rcu_barrier(), but missing from old liburcu versions. */
	synchronize_rcu();
	poll(NULL, 0, 100);
	synchronize_rcu();

	hash_unregister_thread();
	free(tslp);
	pap->nadds = nadds;
	pap->ndels = ndels;
	return NULL;
}

/* Run a performance test. */
void perftest(void)
{
	struct perftest_attr *pap;
	int maxcpus = sysconf(_SC_NPROCESSORS_CONF);
	long i;
	long long nlookups = 0;
	long long nlookupfails = 0;
	long long nadds = 0;
	long long ndels = 0;
	long long starttime;

	BUG_ON(maxcpus <= 0);
	perftest_htp = hashtab_alloc(nbuckets);
	BUG_ON(perftest_htp == NULL);
	hash_register_test(perftest_htp);
	defer_del_done = defer_del_done_perftest;
	pap = malloc(sizeof(*pap) * (nreaders + nupdaters));
	BUG_ON(pap == NULL);
	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nreaders + nupdaters; i++) {
		pap[i].myid = i < nreaders ? i : i - nreaders;
		pap[i].nlookups = 0;
		pap[i].nlookupfails = 0;
		pap[i].nadds = 0;
		pap[i].ndels = 0;
		pap[i].mycpu = (i * cpustride) % maxcpus;
		pap[i].nelements = nupdaters * elperupdater;
		create_thread(i < nreaders ? perftest_reader : perftest_updater,
			      &pap[i]);
	}

	/* Wait for all threads to initialize. */
	while (atomic_read(&nthreads_running) < nreaders + nupdaters)
		poll(NULL, 0, 1);
	smp_mb();

	/* Run the test. */
	starttime = get_microseconds();
	ACCESS_ONCE(goflag) = GOFLAG_RUN;
	poll(NULL, 0, duration);
	ACCESS_ONCE(goflag) = GOFLAG_STOP;
	starttime = get_microseconds() - starttime;
	wait_all_threads();

	/* Collect stats and output them. */
	for (i = 0; i < nreaders + nupdaters; i++) {
		nlookups += pap[i].nlookups;
		nlookupfails += pap[i].nlookupfails;
		nadds += pap[i].nadds;
		ndels += pap[i].ndels;
	}
	printf("nlookups: %lld %lld  nadds: %lld  ndels: %lld  duration: %g\n",
	       nlookups, nlookupfails, nadds, ndels, starttime / 1000.);
	printf("ns/read: %g  ns/update: %g\n",
	       (starttime * 1000. * (double)nreaders) / (double)nlookups,
	       ((starttime * 1000. * (double)nupdaters) /
	        (double)(nadds + ndels)));

	free(pap);
	hashtab_free(perftest_htp);
}


/* Code for Schroedinger's zoo testing. */

#define ZOO_NAMELEN 32
struct zoo_he {
	struct skiplist zhe_e;
	char name[ZOO_NAMELEN];
};

void *zoo_gk(struct skiplist *slep)
{
	struct zoo_he *zhep;

	zhep = container_of(slep, struct zoo_he, zhe_e);
	return (void *)zhep->name;
}

int zoo_cmp(struct skiplist *slep, void *key)
{
	struct zoo_he *zhep;

	zhep = container_of(slep, struct zoo_he, zhe_e);
	return strncmp((char *)key, zhep->name, ZOO_NAMELEN) == 0;
}

unsigned long zoo_hash(char *key)
{
	char *cp = (char *)key;
	int i;
	unsigned long sum = 0;

	for (i = 0; cp[i]; i++)
		sum = sum * 29 + cp[i];
	return sum;
}

/* Look up a key in the Schroedinger-zoo hash table. */
int zoo_lookup(char *key)
{
	unsigned long hash = zoo_hash(key);
	struct skiplist *slep;
	struct zoo_he *zhep;

	hashtab_lock_lookup(perftest_htp, hash);
	slep = hashtab_lookup(perftest_htp, hash, key, zoo_cmp);
	zhep = container_of(slep, struct zoo_he, zhe_e);
	BUG_ON(slep &&
	       (slep->hte_hash != hash ||
	        strncmp(zhep->name, (char *)key, ZOO_NAMELEN) != 0));
	hashtab_unlock_lookup(perftest_htp, hash);
	return !!slep;
}

/* Add an element to the hash table. */
void zoo_add(struct zoo_he *zhep)
{
	unsigned long hash = zoo_hash(zhep->name);

	hashtab_lock_mod(perftest_htp, hash);
	BUG_ON(hashtab_lookup(perftest_htp, hash,
			      (void *)zhep->name, zoo_cmp));
	hashtab_add(perftest_htp, hash, &zhep->zhe_e);
	hashtab_unlock_mod(perftest_htp, hash);
}

/* Remove an element from the hash table. */
void zoo_del(struct zoo_he *zhep)
{
	unsigned long hash = zoo_hash(zhep->name);

	hashtab_lock_mod(perftest_htp, hash);
	hashtab_del(&zhep->zhe_e);
	hashtab_unlock_mod(perftest_htp, hash);
	defer_del(&zhep->zhe_e);
}

char *zoo_names;

/* Schroedinger test reader thread. */
void *zoo_reader(void *arg)
{
	char *cp;
	int gf;
	long i;
	struct perftest_attr *pap = arg;
	long mydelta = primes[pap->myid]; /* Force different reader paths. */
	long ne = pap->nelements;
	int offset = (ne / mydelta) * mydelta == ne;
	long long nlookups = 0;
	long long nlookupfails = 0;

	run_on(pap->mycpu);
	hash_register_thread();

	/* Warm up cache. */
	for (i = 0; i < ne; i++)
		zoo_lookup(&zoo_names[ZOO_NAMELEN * i]);

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
			}
		}
		if (pap->cat)
			cp = "cat";
		else
			cp = &zoo_names[ZOO_NAMELEN * i];
		if (!zoo_lookup(cp))
			nlookupfails++;
		nlookups++;
		i += mydelta;
		if (i >= ne)
			i = i % ne + offset;
	}
	/* Really want rcu_barrier(), but missing from old liburcu versions. */
	synchronize_rcu();
	poll(NULL, 0, 100);
	synchronize_rcu();

	pap->nlookups = nlookups;
	pap->nlookupfails = nlookupfails;
	hash_unregister_thread();
	return NULL;
}

/* Performance test updater thread. */
void *zoo_updater(void *arg)
{
	long i;
	long j;
	int gf;
	struct perftest_attr *pap = arg;
	int myid = pap->myid;
	int mylowkey = myid * elperupdater;
	struct zoo_he *zhep;
	struct zoo_he **zheplist;
	long long nadds = 0;
	long long ndels = 0;

	zheplist = malloc(sizeof(struct zoo_he *) * elperupdater);
	BUG_ON(!zheplist);
	for (i = 0; i < elperupdater; i++)
		zheplist[i] = NULL;
	run_on(pap->mycpu);
	hash_register_thread();

	/* Start with some random half of the elements in the hash table. */
	for (i = 0; i < elperupdater / 2; i++) {
		j = random() % elperupdater;
		while (zheplist[j])
			if (++j >= elperupdater)
				j = 0;
		zhep = malloc(sizeof(*zhep));
		BUG_ON(!zhep);
		strcpy(zhep->name, &zoo_names[ZOO_NAMELEN * (j + mylowkey)]);
		zoo_add(zhep);
		zheplist[j] = zhep;
	}

	/* Announce our presence and enter the test loop. */
	atomic_inc(&nthreads_running);
	i = 0;
	for (;;) {
		gf = ACCESS_ONCE(goflag);
		if (gf != GOFLAG_RUN) {
			if (gf == GOFLAG_STOP)
				break;
			if (gf == GOFLAG_INIT) {
				/* Still initializing, kill statistics. */
				nadds = 0;
				ndels = 0;
			}
		}
		if (updatewait == 0) {
			poll(NULL, 0, 10);  /* No actual updating wanted. */
		} else if (zheplist[i]) {
			zoo_del(zheplist[i]);
			zheplist[i] = NULL;
			ndels++;
		} else {
			zhep = malloc(sizeof(*zhep));
			BUG_ON(!zhep);
			strcpy(zhep->name,
			       &zoo_names[ZOO_NAMELEN * (i + mylowkey)]);
			zoo_add(zhep);
			zheplist[i] = zhep;
			nadds++;
		}

		/* Add requested delay. */
		if (updatewait < 0) {
			poll(NULL, 0, -updatewait);
		} else {
			for (j = 0; j < updatewait; j++)
				barrier();
		}
		if (++i >= elperupdater)
			i = 0;
		if ((i & 0xf) == 0)
			quiescent_state();
	}

	/* Test over, so remove all our elements from the hash table. */
	for (i = 0; i < elperupdater; i++) {
		if (!zheplist[i])
			continue;
		zoo_del(zheplist[i]);
	}
	hash_unregister_thread();
	pap->nadds = nadds;
	pap->ndels = ndels;
	return NULL;
}

void defer_del_free(struct skiplist *slep)
{
	struct zoo_he *zhep = container_of(slep, struct zoo_he, zhe_e);

	free(zhep);
}

/* Run a performance test. */
void zoo_test(void)
{
	struct perftest_attr *pap;
	int maxcpus = sysconf(_SC_NPROCESSORS_CONF);
	long i;
	long long nlookups = 0;
	long long ncatlookups = 0;
	long long nlookupfails = 0;
	long long nadds = 0;
	long long ndels = 0;
	long long starttime;
	struct zoo_he *zhep;

	BUG_ON(maxcpus <= 0);
	perftest_htp = hashtab_alloc(nbuckets);
	BUG_ON(perftest_htp == NULL);
	hash_register_test(perftest_htp);
	defer_del_done = defer_del_free;
	zoo_names = malloc(ZOO_NAMELEN * nupdaters * elperupdater);
	BUG_ON(zoo_names == NULL);
	for (i = 0; i < nupdaters * elperupdater; i++) {
		sprintf(&zoo_names[ZOO_NAMELEN * i], "a%ld", i);
	}

	zhep = malloc(sizeof(*zhep));
	BUG_ON(!zhep);
	strcpy(zhep->name, "cat");
	zoo_add(zhep);

	pap = malloc(sizeof(*pap) * (nreaders + nupdaters));
	BUG_ON(pap == NULL);
	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nreaders + nupdaters; i++) {
		pap[i].myid = i < nreaders ? i : i - nreaders;
		pap[i].cat = i < ncats;
		pap[i].nlookups = 0;
		pap[i].nlookupfails = 0;
		pap[i].nadds = 0;
		pap[i].ndels = 0;
		pap[i].mycpu = (i * cpustride) % maxcpus;
		pap[i].nelements = nupdaters * elperupdater;
		create_thread(i < nreaders ? zoo_reader : zoo_updater, &pap[i]);
	}

	/* Wait for all threads to initialize. */
	while (atomic_read(&nthreads_running) < nreaders + nupdaters)
		poll(NULL, 0, 1);
	smp_mb();

	/* Run the test. */
	starttime = get_microseconds();
	ACCESS_ONCE(goflag) = GOFLAG_RUN;
	poll(NULL, 0, duration);
	ACCESS_ONCE(goflag) = GOFLAG_STOP;
	starttime = get_microseconds() - starttime;
	wait_all_threads();

	/* Collect stats and output them. */
	for (i = 0; i < nreaders + nupdaters; i++) {
		nlookups += pap[i].nlookups;
		if (pap[i].cat)
			ncatlookups += pap[i].nlookups;
		nlookupfails += pap[i].nlookupfails;
		nadds += pap[i].nadds;
		ndels += pap[i].ndels;
	}
	printf("nlookups: %lld %lld  ncats: %lld  nadds: %lld  ndels: %lld  duration: %g\n",
	       nlookups, nlookupfails, ncatlookups, nadds, ndels, starttime / 1000.);
	printf("ns/read: %g  ns/update: %g\n",
	       (starttime * 1000. * (double)nreaders) / (double)nlookups,
	       ((starttime * 1000. * (double)nupdaters) /
	        (double)(nadds + ndels)));
}


/* Common argument-parsing code. */

void usage(char *progname, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vfprintf(stderr, format, ap);
	va_end(ap);
	fprintf(stderr, "Usage: %s --smoketest\n", progname);
	fprintf(stderr, "Usage: %s --perftest\n", progname);
	fprintf(stderr, "Usage: %s --schroedinger\n", progname);
	fprintf(stderr, "\t--nbuckets\n");
	fprintf(stderr, "\t\tNumber of buckets, defaults to 1024.\n");
	fprintf(stderr, "\t--ncats\n");
	fprintf(stderr, "\t\tNumber of cat readers, defaults to 0.\n");
	fprintf(stderr, "\t\t(Only for --schroedinger.)\n");
	fprintf(stderr, "\t--nreaders\n");
	fprintf(stderr, "\t\tNumber of readers, defaults to 1.\n");
	fprintf(stderr, "\t--nupdaters\n");
	fprintf(stderr, "\t\tNumber of updaters, defaults to 1.  Must be 1\n");
	fprintf(stderr, "\t\tor greater, or hash table will be empty.\n");
	fprintf(stderr, "\t--updatewait\n");
	fprintf(stderr, "\t\tNumber of spin-loop passes per update,\n");
	fprintf(stderr, "\t\tdefaults to -1.  If 0, the updater will not.\n");
	fprintf(stderr, "\t\tdo any updates, except for initialization.\n");
	fprintf(stderr, "\t\tIf negative, the updater waits for the\n");
	fprintf(stderr, "\t\tcorresponding number of milliseconds\n");
	fprintf(stderr, "\t\tbetween updates.\n");
	fprintf(stderr, "\t--elems/writer\n");
	fprintf(stderr, "\t\tNumber of hash-table elements per writer,\n");
	fprintf(stderr, "\t\tdefaults to 2048.  Must be greater than zero.\n");
	fprintf(stderr, "\t--cpustride\n");
	fprintf(stderr, "\t\tStride when spreading threads across CPUs,\n");
	fprintf(stderr, "\t\tdefaults to 1.\n");
	fprintf(stderr, "\t--resizediv\n");
	fprintf(stderr, "\t\tDivisor for resized hash table,\n");
	fprintf(stderr, "\t\tdefaults to zero (don't resize).\n");
	fprintf(stderr, "\t--resizemult\n");
	fprintf(stderr, "\t\tMultiplier for resized hash table,\n");
	fprintf(stderr, "\t\tdefaults to zero (don't resize).\n");
	fprintf(stderr, "\t--resizewait\n");
	fprintf(stderr, "\t\tMilliseconds to wait between resizes,\n");
	fprintf(stderr, "\t\tdefaults to one.\n");
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds.\n");
	exit(-1);
}

/*
 * Mainprogram.
 */
int main(int argc, char *argv[])
{
	int i = 1;
	void (*test_to_do)(void) = NULL;

	smp_init();
	other_init();

	while (i < argc) {
		if (strcmp(argv[i], "--smoketest") == 0) {
			if (i < argc - 1 || i != 1)
				usage(argv[0],
				      "Excess arguments for %s\n", argv[i]);
			smoketest();
			exit(0);
		} else if (strcmp(argv[i], "--perftest") == 0) {
			test_to_do = perftest;
			if (i != 1)
				usage(argv[0],
				      "Must be first argument: %s\n", argv[i]);
		} else if (strcmp(argv[i], "--schroedinger") == 0) {
			test_to_do = zoo_test;
			if (i != 1)
				usage(argv[0],
				      "Must be first argument: %s\n", argv[i]);
		} else if (strcmp(argv[i], "--nbuckets") == 0) {
			nbuckets = strtol(argv[++i], NULL, 0);
			if (nbuckets < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--nreaders") == 0) {
			nreaders = strtol(argv[++i], NULL, 0);
			if (nreaders < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--ncats") == 0) {
			ncats = strtol(argv[++i], NULL, 0);
			if (ncats < 0 || ncats > nreaders)
				usage(argv[0],
				      "%s must be >= 0 and <= --nreaders\n",
				      argv[i - 1]);
		} else if (strcmp(argv[i], "--nupdaters") == 0) {
			nupdaters = strtol(argv[++i], NULL, 0);
			if (nupdaters < 1)
				usage(argv[0],
				      "%s must be >= 1\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--updatewait") == 0) {
			updatewait = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--elems/writer") == 0) {
			elperupdater = strtol(argv[++i], NULL, 0);
			if (elperupdater < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--cpustride") == 0) {
			cpustride = strtol(argv[++i], NULL, 0);
		} else if (strcmp(argv[i], "--resizediv") == 0) {
			resizediv = strtol(argv[++i], NULL, 0);
			if (resizediv < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
			if (resizediv != 0 && resizemult == 0)
				resizemult = 1;
		} else if (strcmp(argv[i], "--resizemult") == 0) {
			resizemult = strtol(argv[++i], NULL, 0);
			if (resizemult < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
			if (resizemult != 0 && resizediv == 0)
				resizediv = 1;
		} else if (strcmp(argv[i], "--resizewait") == 0) {
			resizewait = strtol(argv[++i], NULL, 0);
			if (resizewait < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = strtol(argv[++i], NULL, 0);
			if (duration < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
		} else {
			usage(argv[0], "Unrecognized argument: %s\n",
			      argv[i]);
		}
		i++;
	}
	if (!test_to_do)
		usage(argv[0], "No test specified\n");
	if (resizediv != 0 && resizemult != 0)
		create_thread(perftest_resize, NULL);
	test_to_do();
	if (resizediv != 0 && resizemult != 0)
		printf("Resizes: %lld\n", nresizes);
	return 0;
}

#else

/* Parameters for performance test. */
int nreaders = 2;
int nupdaters = 5;
int updatewait = 1;
long elperupdater = 2048; /* Allow for them being stuck in grace periods. */
long valsperupdater = 2;
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
	long long nadds;
	long long ndels;
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

	slp = skiplist_lookup_relaxed(&head_sl.sle_e, (void *)i, testcmp);
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
				 (void *)tslp->data, testcmp);
	if (result)
		tslp->in_table = 0;
	return result;
}

/* Remove an element from the skiplist. */
int stresstest_del(unsigned long key)
{
	struct skiplist *slp;
	struct testsl *tslp;

	slp = skiplist_delete(&head_sl.sle_e, (void *)key, testcmp);
	if (!slp)
		return -ENOENT;
	tslp = container_of(slp, struct testsl, sle_e);
	tslp->in_table = 2;
	defer_del(&tslp->rh);
}

/* Stress test reader thread. */
void *stresstest_reader(void *arg)
{
	int gf;
	long i;
	struct stresstest_attr *pap = arg;
	long ne = pap->nelements;
	long long nlookups = 0;
	long long nlookupfails = 0;

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
	}
	pap->nlookups = nlookups;
	pap->nlookupfails = nlookupfails;
	rcu_unregister_thread();
	return NULL;
}

/* Stress test updater thread. */
void *stresstest_updater(void *arg)
{
	long i;
	long j;
	long k;
	int gf;
	struct stresstest_attr *pap = arg;
	int myid = pap->myid;
	int mylowkey = myid * elperupdater;
	struct testsl *tslp;
	long long nadds = 0;
	long long ndels = 0;

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
				ndels = 0;
			}
		}
		if (updatewait == 0) {
			poll(NULL, 0, 10);  /* No actual updating wanted. */
		} else if (tslp[i].in_table == 0) {
			stresstest_add(&tslp[i]);
			nadds++;
			if (++i >= elperupdater)
				i = 0;
			if ((nadds & 0xff) == 0)
				quiescent_state();
		} else {
			stresstest_del((unsigned long)j);
			ndels++;
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
		(void)stresstest_del((unsigned long)i);
	}

	skiplist_lock(&head_sl.sle_e);
	skiplist_fsck(&head_sl.sle_e, testcmp);
	skiplist_unlock(&head_sl.sle_e);

	/* Really want rcu_barrier(), but missing from old liburcu versions. */
	synchronize_rcu();
	poll(NULL, 0, 100);
	synchronize_rcu();

	rcu_unregister_thread();
	free(tslp);
	pap->nadds = nadds;
	pap->ndels = ndels;
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
	long long nadds = 0;
	long long ndels = 0;
	long long starttime;
	long long endtime;

	BUG_ON(maxcpus <= 0);
	rcu_register_thread();
	skiplist_init(&head_sl.sle_e);
	defer_del_done = defer_del_done_stresstest;
	pap = malloc(sizeof(*pap) * (nreaders + nupdaters));
	BUG_ON(pap == NULL);
	atomic_set(&nthreads_running, 0);
	goflag = GOFLAG_INIT;

	for (i = 0; i < nreaders + nupdaters; i++) {
		pap[i].myid = i < nreaders ? i : i - nreaders;
		pap[i].nlookups = 0;
		pap[i].nlookupfails = 0;
		pap[i].nadds = 0;
		pap[i].ndels = 0;
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

	/* Collect stats and output them. */
	for (i = 0; i < nreaders + nupdaters; i++) {
		nlookups += pap[i].nlookups;
		nlookupfails += pap[i].nlookupfails;
		nadds += pap[i].nadds;
		ndels += pap[i].ndels;
	}
	printf("nlookups: %lld %lld  nadds: %lld  ndels: %lld  duration: %g\n",
	       nlookups, nlookupfails, nadds, ndels, starttime / 1000.);
	printf("ns/read: %g  ns/update: %g\n",
	       (starttime * 1000. * (double)nreaders) / (double)nlookups,
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
	fprintf(stderr, "\t--debug\n");
	fprintf(stderr, "\t\tEnable additional debug checks..\n");
	fprintf(stderr, "\t--duration\n");
	fprintf(stderr, "\t\tDuration of test, in milliseconds.\n");
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
		} else if (strcmp(argv[i], "--debug") == 0) {
			debug = 1;
		} else if (strcmp(argv[i], "--duration") == 0) {
			duration = strtol(argv[++i], NULL, 0);
			if (duration < 0)
				usage(argv[0],
				      "%s must be >= 0\n", argv[i - 1]);
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

#endif
