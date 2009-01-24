/*
 * lockdeq.c: simple lock-based parallel deq implementation.
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"

/*
 * Deq structure, empty list:
 *
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *     |   |   |   |   |   |   |   |   |   |   |   |   |   |   |   |
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *                               ^   ^
 *                               |   |
 *                            lidx   ridx
 *
 *
 * List after three deq_enqueue_l() invocations of "a", "b", and "c":
 *
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *     |   |   |   |   | c | b | a |   |   |   |   |   |   |   |   |
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *                   ^               ^
 *                   |               |
 *                lidx               ridx
 *
 * List after one deq_dequeue_r() invocations (removing "a"):
 *
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *     |   |   |   |   | c | b |   |   |   |   |   |   |   |   |   |
 *     +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *                   ^           ^
 *                   |           |
 *                lidx           ridx
 *
 * This is pretty standard.  The trick is that only the low-order bits
 * of lidx and ridx are used to index into a power-of-two sized hash
 * table.  Each bucket of the hash table is a circular doubly linked
 * list (AKA Linux-kernel list_head structure).  Left-hand operations
 * manipulate the tail of the selected list, while right-hand operations
 * manipulate the head of the selected list.  Each bucket has its own
 * lock, minimizing lock contention.  Each of the two indexes also has
 * its own lock.
 */

/*
 * This must be a power of two.  If you want something else, also adjust
 * the moveleft() and moveright() functions.
 */
#define DEQ_N_BKTS 4

struct deq_bkt {
	spinlock_t lock;
	struct list_head chain;
} ____cacheline_internodealigned_in_smp;

struct deq {
	spinlock_t llock;
	int lidx;
	/* char pad1[CACHE_LINE_SIZE - sizeof(spinlock_t) - sizeof(int)]; */
	spinlock_t rlock ____cacheline_internodealigned_in_smp;
	int ridx;
	/* char pad2[CACHE_LINE_SIZE - sizeof(spinlock_t) - sizeof(int)]; */
	struct deq_bkt bkt[DEQ_N_BKTS];
};

static int moveleft(int idx)
{
	return (idx - 1) & (DEQ_N_BKTS - 1);
}

static int moveright(int idx)
{
	return (idx + 1) & (DEQ_N_BKTS - 1);
}

void init_deq(struct deq *d)
{
	int i;

	d->lidx = 0;
	spin_lock_init(&d->llock);
	d->ridx = 1;
	spin_lock_init(&d->rlock);
	for (i = 0; i < DEQ_N_BKTS; i++) {
		spin_lock_init(&d->bkt[i].lock);
		INIT_LIST_HEAD(&d->bkt[i].chain);
	}
}

struct list_head *deq_dequeue_l(struct deq *d)
{
	struct list_head *e;
	int i;
	struct deq_bkt *p;

	spin_lock(&d->llock);
	i = moveright(d->lidx);
	p = &d->bkt[i];
	spin_lock(&p->lock);
	if (list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.prev;
		list_del_init(e);
		d->lidx = i;
	}
	spin_unlock(&p->lock);
	spin_unlock(&d->llock);
	return e;
}

struct list_head *deq_dequeue_r(struct deq *d)
{
	struct list_head *e;
	int i;
	struct deq_bkt *p;

	spin_lock(&d->rlock);
	i = moveleft(d->ridx);
	p = &d->bkt[i];
	spin_lock(&p->lock);
	if (list_empty(&p->chain))
		e = NULL;
	else {
		e = p->chain.next;
		list_del_init(e);
		d->ridx = i;
	}
	spin_unlock(&d->bkt[i].lock);
	spin_unlock(&d->rlock);
	return e;
}

void deq_enqueue_l(struct list_head *e, struct deq *d)
{
	int i;
	struct deq_bkt *p;

	spin_lock(&d->llock);
	i = d->lidx;
	p = &d->bkt[i];
	spin_lock(&p->lock);
	list_add_tail(e, &p->chain);
	d->lidx = moveleft(d->lidx);
	spin_unlock(&p->lock);
	spin_unlock(&d->llock);
}

void deq_enqueue_r(struct list_head *e, struct deq *d)
{
	int i;
	struct deq_bkt *p;

	spin_lock(&d->rlock);
	i = d->ridx;
	p = &d->bkt[i];
	spin_lock(&p->lock);
	list_add(e, &p->chain);
	d->ridx = moveright(d->ridx);
	spin_unlock(&p->lock);
	spin_unlock(&d->rlock);
}

#ifdef TEST

#define N_TEST_ELEMS 10

struct deq_elem {
	struct list_head l;
	int data;
};

#define GOFLAG_INIT	0
#define GOFLAG_START	1
#define GOFLAG_STOP	2

struct deq_test {
	void (*enqueue)(struct list_head *e, struct deq *d);
	struct list_head *(*dequeue)(struct deq *d);
	struct deq *d;
	struct deq_elem *p;
	struct deq_elem **q;
	int nelem;
	int datastart;
	int datainc;
	atomic_t *count;
	int *goflag;
};

void deq_enqueue_error(struct list_head *e, struct deq *d)
{
	printf("deq_enqueue_error()\n");
	abort();
}

struct list_head *deq_dequeue_error(struct deq *d)
{
	printf("deq_dequeue_error()\n");
	abort();
}

/*
 * Enqueue elements as specified by the deq_test structure.  This may
 * either be called directly (with the specified goflag already set
 * to GOFLAG_START) or via create_thread().
 */
void *concurrent_enqueue(void *arg)
{
	struct deq_test *t = (struct deq_test *)arg;
	int i;
	struct deq_elem *p = t->p;
	int v = t->datastart;

	atomic_inc(t->count);
	while (*t->goflag == GOFLAG_INIT)
		barrier();

	for (i = 0; i < t->nelem; i++) {
		p[i].data = v;
		t->enqueue(&p[i].l, t->d);
		v += t->datainc;
	}
	return (NULL);
}

/*
 * Dequeue as specified by the deq_test structure. This may be called
 * directly (in which case the number of elements to be dequeued must
 * be exactly that required and the specified goflag already set to
 * GOFLAG_START), or via create_thread.
 */
void *concurrent_dequeue(void *arg)
{
	struct deq_test *t = (struct deq_test *)arg;
	int i;
	struct list_head *p0;
	struct deq_elem *p1;

	atomic_inc(t->count);
	while (*t->goflag == GOFLAG_INIT)
		barrier();

	i = 0;
	while (*t->goflag == GOFLAG_START) {
		if (i == t->nelem)
			break;
		p0 = t->dequeue(t->d);
		if (p0 == NULL)
			continue;
		p1 = list_entry(p0, struct deq_elem, l);
		t->q[i++] = p1;
	}
	return (void *)i;
}

/*
 * Variable declarations required for the pair-wise enqueue tests.
 */
#define PAIRWISE_VAR_DEFS() \
	atomic_t count; \
	struct deq d; \
	struct deq_test dtenq1; \
	struct deq_test dtenq2; \
	struct deq_test dtdeq1; \
	struct deq_elem dtelem1[N_TEST_ELEMS]; \
	struct deq_elem dtelem2[N_TEST_ELEMS]; \
	struct deq_elem *dtelemdeq[2 * N_TEST_ELEMS]; \
	int goflag


/*
 * Initialize a deq_test structure for enqueuing.
 * The caller must provide a struct deq named "d", an atomic_t named
 * "count", and an int named "goflag".
 */
#define INIT_ENQUEUE(dt, f, ea, start, inc) \
do { \
	dt.enqueue = &f; \
	dt.dequeue = &deq_dequeue_error; \
	dt.d = &d; \
	dt.p = ea; \
	dt.nelem = sizeof(ea) / sizeof(ea[0]); \
	dt.datastart = start; \
	dt.datainc = inc; \
	dt.count = &count; \
	dt.goflag = &goflag; \
} while (0)

/*
 * Initialize a deq_test structure for enqueuing.
 * The caller must provide a struct deq named "d", an atomic_t named
 * "count", and an int named "goflag".
 */
#define INIT_DEQUEUE(dt, f, epa) \
do { \
	dt.enqueue = &deq_enqueue_error; \
	dt.dequeue = &f; \
	dt.d = &d; \
	dt.q = epa; \
	dt.nelem = sizeof(epa) / sizeof(epa[0]); \
	dt.count = &count; \
	dt.goflag = &goflag; \
} while (0)

/*
 * Run a pair of enqueue threads on the specified deq_test structures.
 * The caller must supply an atomic_t "count" and an int "goflag".
 */
#define RUN_ENQUEUE_PAIR(dte1, dte2) \
do { \
	goflag = GOFLAG_INIT; \
	atomic_set(&count, 0); \
	create_thread(concurrent_enqueue, (void *)&dte1); \
	create_thread(concurrent_enqueue, (void *)&dte2); \
	while (atomic_read(&count) < 2) \
		barrier(); \
	goflag = GOFLAG_START; \
	wait_all_threads(); \
} while (0)

/*
 * Check a sequence of elements removed from a dequeue.  These must have
 * been inserted by a pair of threads, one of which enqueued positive
 * elements and the other negative, such that the first element dequeued
 * is either +1 or -1.
 */
#define CHECK_SEQUENCE_PAIR(dtelemdeq) \
do { \
	int i; \
	int ipos = 0; \
	int ineg = 0; \
	\
	atomic_set(&count, 0); \
	goflag = GOFLAG_START; \
	if ((i = (long)concurrent_dequeue(&dtdeq1)) != dtdeq1.nelem) { \
		printf("Expected to dequeue %d, got %d\n", \
		       dtdeq1.nelem, i); \
		abort(); \
	} \
	\
	for (i = 0; i < sizeof(dtelemdeq) / sizeof(dtelemdeq[0]); i++) { \
		int icheck = dtelemdeq[i]->data; \
		\
		printf("%d ", icheck); \
		if (icheck < 0) { \
			if (icheck != --ineg) { \
				printf("Neg seq err: expected %d, got %d\n", \
				       ineg, icheck); \
				abort(); \
			} \
		} else if (icheck != ++ipos) { \
			printf("Pos seq err: expected %d, got %d\n", \
			       ipos, icheck); \
			abort(); \
		} \
	} \
	printf("OK\n"); \
} while (0)

void conc_enq_l(void)
{
	PAIRWISE_VAR_DEFS();

	printf("Concurrently enqueue L, dequeue R\n");

	init_deq(&d);

	INIT_ENQUEUE(dtenq1, deq_enqueue_l, dtelem1, 1, 1);
	INIT_ENQUEUE(dtenq2, deq_enqueue_l, dtelem2, -1, -1);
	RUN_ENQUEUE_PAIR(dtenq1, dtenq2);

	INIT_DEQUEUE(dtdeq1, deq_dequeue_r, dtelemdeq);
	CHECK_SEQUENCE_PAIR(dtelemdeq);
}

void conc_enq_r(void)
{
	PAIRWISE_VAR_DEFS();

	printf("Concurrently enqueue R, dequeue L\n");

	init_deq(&d);

	INIT_ENQUEUE(dtenq1, deq_enqueue_r, dtelem1, 1, 1);
	INIT_ENQUEUE(dtenq2, deq_enqueue_r, dtelem2, -1, -1);
	RUN_ENQUEUE_PAIR(dtenq1, dtenq2);

	INIT_DEQUEUE(dtdeq1, deq_dequeue_l, dtelemdeq);
	CHECK_SEQUENCE_PAIR(dtelemdeq);
}

void conc_push_l(void)
{
	PAIRWISE_VAR_DEFS();

	printf("Concurrently push L\n");

	init_deq(&d);

	INIT_ENQUEUE(dtenq1, deq_enqueue_r, dtelem1, N_TEST_ELEMS, -1);
	INIT_ENQUEUE(dtenq2, deq_enqueue_r, dtelem2, -N_TEST_ELEMS, 1);
	RUN_ENQUEUE_PAIR(dtenq1, dtenq2);

	INIT_DEQUEUE(dtdeq1, deq_dequeue_r, dtelemdeq);
	CHECK_SEQUENCE_PAIR(dtelemdeq);
}

void conc_push_r(void)
{
	PAIRWISE_VAR_DEFS();

	printf("Concurrently push R\n");

	init_deq(&d);

	INIT_ENQUEUE(dtenq1, deq_enqueue_l, dtelem1, N_TEST_ELEMS, -1);
	INIT_ENQUEUE(dtenq2, deq_enqueue_l, dtelem2, -N_TEST_ELEMS, 1);
	RUN_ENQUEUE_PAIR(dtenq1, dtenq2);

	INIT_DEQUEUE(dtdeq1, deq_dequeue_l, dtelemdeq);
	CHECK_SEQUENCE_PAIR(dtelemdeq);
}

void melee(void)
{
	atomic_t count;
	struct deq d;
	struct deq_test dtenq1;
	struct deq_test dtenq2;
	struct deq_test dtdeq1;
	struct deq_test dtdeq2;
	struct deq_elem dtelem1[N_TEST_ELEMS];
	struct deq_elem dtelem2[N_TEST_ELEMS];
	struct deq_elem *dtelemdeq1[2 * N_TEST_ELEMS] = { NULL };
	struct deq_elem *dtelemdeq2[2 * N_TEST_ELEMS] = { NULL };
	int goflag;
	int i;
	char check[2 * N_TEST_ELEMS + 1] = { 0 };

	printf("Concurrent melee between a pair of enqueues and of dequeues\n");

	init_deq(&d);

	INIT_ENQUEUE(dtenq1, deq_enqueue_l, dtelem1, 1, 1);
	INIT_ENQUEUE(dtenq2, deq_enqueue_r, dtelem2, -1, -1);
	INIT_DEQUEUE(dtdeq1, deq_dequeue_l, dtelemdeq1);
	INIT_DEQUEUE(dtdeq2, deq_dequeue_l, dtelemdeq2);

	goflag = GOFLAG_INIT;
	atomic_set(&count, 0);
	create_thread(concurrent_enqueue, (void *)&dtenq1);
	create_thread(concurrent_enqueue, (void *)&dtenq2);
	create_thread(concurrent_dequeue, (void *)&dtdeq1);
	create_thread(concurrent_dequeue, (void *)&dtdeq2);
	while (atomic_read(&count) < 4)
		barrier();
	goflag = GOFLAG_START;
	sleep(3);
	goflag = GOFLAG_STOP;
	wait_all_threads();

	for (i = 0; i < 2 * N_TEST_ELEMS; i++) {
		if (dtelemdeq1[i] != NULL) {
			printf("%d ", dtelemdeq1[i]->data);
			if (check[dtelemdeq1[i]->data + N_TEST_ELEMS] != 0)
				abort();
			check[dtelemdeq1[i]->data + N_TEST_ELEMS] = 1;
		}
		if (dtelemdeq2[i] != NULL) {
			printf("%d ", dtelemdeq2[i]->data);
			if (check[dtelemdeq2[i]->data + N_TEST_ELEMS] != 0)
				abort();
			check[dtelemdeq2[i]->data + N_TEST_ELEMS] = 1;
		}
	}
	printf("\n");
	for (i = -N_TEST_ELEMS + 1; i < N_TEST_ELEMS; i++) {
		if (i == 0)
			continue;
		if (!check[i + N_TEST_ELEMS])
			abort();
	}
}

int getdata(struct list_head *p)
{
	if (p == NULL)
		return 0;
	return list_entry(p, struct deq_elem, l)->data;
}

int main(int argc, char *argv[])
{
	int d1, d2, d3, d4;
	struct deq_elem e1, e2, e3;
	struct list_head *p;
	struct deq dequeue;

	init_deq(&dequeue);
	printf("Empty dequeue: L: %p, R: %p\n",
	       deq_dequeue_l(&dequeue), deq_dequeue_r(&dequeue));

	e1.data = 1;
	e2.data = 2;
	e3.data = 3;
	deq_enqueue_l(&e1.l, &dequeue);
	deq_enqueue_l(&e2.l, &dequeue);
	deq_enqueue_l(&e3.l, &dequeue);
	d1 = getdata(deq_dequeue_l(&dequeue));
	d2 = getdata(deq_dequeue_l(&dequeue));
	d3 = getdata(deq_dequeue_l(&dequeue));
	d4 = getdata(deq_dequeue_l(&dequeue));
	printf("Enqueue L, dequeue L: %d %d %d %d\n", d1, d2, d3, d4);

	deq_enqueue_l(&e3.l, &dequeue);
	deq_enqueue_l(&e2.l, &dequeue);
	deq_enqueue_l(&e1.l, &dequeue);
	d1 = getdata(deq_dequeue_r(&dequeue));
	d2 = getdata(deq_dequeue_r(&dequeue));
	d3 = getdata(deq_dequeue_r(&dequeue));
	d4 = getdata(deq_dequeue_r(&dequeue));
	printf("Enqueue L, dequeue R: %d %d %d %d\n", d1, d2, d3, d4);


	deq_enqueue_r(&e3.l, &dequeue);
	deq_enqueue_r(&e2.l, &dequeue);
	deq_enqueue_r(&e1.l, &dequeue);
	d1 = getdata(deq_dequeue_l(&dequeue));
	d2 = getdata(deq_dequeue_l(&dequeue));
	d3 = getdata(deq_dequeue_l(&dequeue));
	d4 = getdata(deq_dequeue_l(&dequeue));
	printf("Enqueue R, dequeue L: %d %d %d %d\n", d1, d2, d3, d4);

	e1.data = 1;
	e2.data = 2;
	e3.data = 3;
	deq_enqueue_r(&e1.l, &dequeue);
	deq_enqueue_r(&e2.l, &dequeue);
	deq_enqueue_r(&e3.l, &dequeue);
	d1 = getdata(deq_dequeue_r(&dequeue));
	d2 = getdata(deq_dequeue_r(&dequeue));
	d3 = getdata(deq_dequeue_r(&dequeue));
	d4 = getdata(deq_dequeue_r(&dequeue));
	printf("Enqueue R, dequeue R: %d %d %d %d\n", d1, d2, d3, d4);

	conc_enq_l();
	conc_enq_r();
	conc_push_l();
	conc_push_r();
	melee();
}
#endif /* #ifdef TEST */
