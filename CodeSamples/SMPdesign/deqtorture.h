/*
 * deqtorture.h: torture tests for double-ended queue.
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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#define N_TEST_ELEMS 10

struct deq_elem {
	struct cds_list_head l;
	int data;
};

#define GOFLAG_INIT	0
#define GOFLAG_START	1
#define GOFLAG_STOP	2

struct deq_test {
	void (*push)(struct cds_list_head *e, struct pdeq *d);
	struct cds_list_head *(*pop)(struct pdeq *d);
	struct pdeq *d;
	struct deq_elem *p;
	struct deq_elem **q;
	int nelem;
	int datastart;
	int datainc;
	atomic_t *count;
	int *goflag;
	long long endtime;
};

void pdeq_push_error(struct cds_list_head *e, struct pdeq *d)
{
	printf("pdeq_push_error()\n");
	abort();
}

struct cds_list_head *pdeq_pop_error(struct pdeq *d)
{
	printf("pdeq_pop_error()\n");
	abort();
}

/*
 * Enqueue elements as specified by the deq_test structure.  This may
 * either be called directly (with the specified goflag already set
 * to GOFLAG_START) or via create_thread().
 */
void *concurrent_ppush(void *arg)
{
	struct deq_test *t = (struct deq_test *)arg;
	int i;
	int me;
	struct deq_elem *p = t->p;
	int v = t->datastart;

	me = atomic_add_return(1, t->count) + 1;
	run_on(me);
	while (*t->goflag == GOFLAG_INIT)
		barrier();

	for (i = 0; i < t->nelem; i++) {
		p[i].data = v;
		t->push(&p[i].l, t->d);
		v += t->datainc;
	}
	return (NULL);
}

/*
 * Dequeue as specified by the deq_test structure. This may be called
 * directly (in which case the number of elements to be popped must
 * be exactly that required and the specified goflag already set to
 * GOFLAG_START), or via create_thread.
 */
void *concurrent_ppop(void *arg)
{
	struct deq_test *t = (struct deq_test *)arg;
	int i;
	int me;
	struct cds_list_head *p0;
	struct deq_elem *p1;

	me = atomic_add_return(1, t->count) + 1;
	run_on(me);
	while (*t->goflag == GOFLAG_INIT)
		barrier();

	i = 0;
	while (*t->goflag == GOFLAG_START) {
		if (i == t->nelem)
			break;
		p0 = t->pop(t->d);
		if (p0 == NULL)
			continue;
		p1 = cds_list_entry(p0, struct deq_elem, l);
		t->q[i++] = p1;
	}
	t->endtime = get_microseconds();
	return (void *)(long)i;
}

/*
 * Variable declarations required for the pair-wise push tests.
 */
#define PAIRWISE_VAR_DEFS() \
	atomic_t count; \
	struct pdeq d; \
	struct deq_test dtenq1; \
	struct deq_test dtenq2; \
	struct deq_test dtdeq1; \
	struct deq_elem dtelem1[N_TEST_ELEMS]; \
	struct deq_elem dtelem2[N_TEST_ELEMS]; \
	struct deq_elem *dtelemdeq[2 * N_TEST_ELEMS]; \
	int goflag


/*
 * Initialize a deq_test structure for enqueuing.
 * The caller must provide a struct pdeq named "d", an atomic_t named
 * "count", and an int named "goflag".
 */
#define INIT_ENQUEUE(dt, f, ea, start, inc) \
do { \
	dt.push = &f; \
	dt.pop = &pdeq_pop_error; \
	dt.d = &d; \
	dt.p = ea; \
	dt.nelem = sizeof(ea) / sizeof(ea[0]); \
	dt.datastart = start; \
	dt.datainc = inc; \
	dt.count = &count; \
	dt.goflag = &goflag; \
} while (0)

/*
 * Initialize a deq_test structure for dequeuing.
 * The caller must provide a struct pdeq named "d", an atomic_t named
 * "count", and an int named "goflag".
 */
#define INIT_DEQUEUE(dt, f, epa) \
do { \
	dt.push = &pdeq_push_error; \
	dt.pop = &f; \
	dt.d = &d; \
	dt.q = epa; \
	dt.nelem = sizeof(epa) / sizeof(epa[0]); \
	dt.count = &count; \
	dt.goflag = &goflag; \
} while (0)

/*
 * Run a pair of push threads on the specified deq_test structures.
 * The caller must supply an atomic_t "count" and an int "goflag".
 */
#define RUN_ENQUEUE_PAIR(dte1, dte2) \
do { \
	goflag = GOFLAG_INIT; \
	atomic_set(&count, 0); \
	create_thread(concurrent_ppush, (void *)&dte1); \
	create_thread(concurrent_ppush, (void *)&dte2); \
	while (atomic_read(&count) < 2) \
		barrier(); \
	goflag = GOFLAG_START; \
	wait_all_threads(); \
} while (0)

/*
 * Check a sequence of elements removed from a deque.  These must have
 * been inserted by a pair of threads, one of which pushed positive
 * elements and the other negative, such that the first element popped
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
	if ((i = (long)concurrent_ppop(&dtdeq1)) != dtdeq1.nelem) { \
		printf("Expected to pop %d, got %d\n", \
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

	printf("Concurrently push L, pop R\n");

	init_pdeq(&d);

	INIT_ENQUEUE(dtenq1, pdeq_push_l, dtelem1, 1, 1);
	INIT_ENQUEUE(dtenq2, pdeq_push_l, dtelem2, -1, -1);
	RUN_ENQUEUE_PAIR(dtenq1, dtenq2);

	INIT_DEQUEUE(dtdeq1, pdeq_pop_r, dtelemdeq);
	CHECK_SEQUENCE_PAIR(dtelemdeq);
}

void conc_enq_r(void)
{
	PAIRWISE_VAR_DEFS();

	printf("Concurrently push R, pop L\n");

	init_pdeq(&d);

	INIT_ENQUEUE(dtenq1, pdeq_push_r, dtelem1, 1, 1);
	INIT_ENQUEUE(dtenq2, pdeq_push_r, dtelem2, -1, -1);
	RUN_ENQUEUE_PAIR(dtenq1, dtenq2);

	INIT_DEQUEUE(dtdeq1, pdeq_pop_l, dtelemdeq);
	CHECK_SEQUENCE_PAIR(dtelemdeq);
}

void conc_push_l(void)
{
	PAIRWISE_VAR_DEFS();

	printf("Concurrently push L\n");

	init_pdeq(&d);

	INIT_ENQUEUE(dtenq1, pdeq_push_r, dtelem1, N_TEST_ELEMS, -1);
	INIT_ENQUEUE(dtenq2, pdeq_push_r, dtelem2, -N_TEST_ELEMS, 1);
	RUN_ENQUEUE_PAIR(dtenq1, dtenq2);

	INIT_DEQUEUE(dtdeq1, pdeq_pop_r, dtelemdeq);
	CHECK_SEQUENCE_PAIR(dtelemdeq);
}

void conc_push_r(void)
{
	PAIRWISE_VAR_DEFS();

	printf("Concurrently push R\n");

	init_pdeq(&d);

	INIT_ENQUEUE(dtenq1, pdeq_push_l, dtelem1, N_TEST_ELEMS, -1);
	INIT_ENQUEUE(dtenq2, pdeq_push_l, dtelem2, -N_TEST_ELEMS, 1);
	RUN_ENQUEUE_PAIR(dtenq1, dtenq2);

	INIT_DEQUEUE(dtdeq1, pdeq_pop_l, dtelemdeq);
	CHECK_SEQUENCE_PAIR(dtelemdeq);
}

void melee(void)
{
	atomic_t count;
	struct pdeq d;
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
	int ok = 1;
	char check[2 * N_TEST_ELEMS + 1] = { 0 };

	printf("Concurrent melee between a pair of pushes and of pops\n");

	init_pdeq(&d);

	INIT_ENQUEUE(dtenq1, pdeq_push_l, dtelem1, 1, 1);
	INIT_ENQUEUE(dtenq2, pdeq_push_r, dtelem2, -1, -1);
	INIT_DEQUEUE(dtdeq1, pdeq_pop_l, dtelemdeq1);
	INIT_DEQUEUE(dtdeq2, pdeq_pop_l, dtelemdeq2);

	goflag = GOFLAG_INIT;
	atomic_set(&count, 0);
	create_thread(concurrent_ppush, (void *)&dtenq1);
	create_thread(concurrent_ppush, (void *)&dtenq2);
	create_thread(concurrent_ppop, (void *)&dtdeq1);
	create_thread(concurrent_ppop, (void *)&dtdeq2);
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
	for (i = -N_TEST_ELEMS; i < N_TEST_ELEMS + 1; i++) {
		if (i == 0)
			continue;
		if (!check[i + N_TEST_ELEMS]) {
			printf("Missing element %d\n", i);
			ok = 0;
		}
	}
	if (!ok)
		abort();
	printf("OK\n");
}

#define N_PERF_MSGS (1000*1000)
#define N_PERF_HEADSTART (N_PERF_MSGS / 100)

struct deq_elem msgxmitarray[N_PERF_MSGS];
struct deq_elem *msgrecvarray[N_PERF_MSGS];

void simple_deq_perf(void)
{
	struct cds_list_head d;
	int i;
	struct cds_list_head *p;
	long long starttime;
	long long stoptime;

	printf("Push %d elements sequentially through a cds_list_head\n",
	       N_PERF_MSGS);
	CDS_INIT_LIST_HEAD(&d);
	starttime = get_microseconds();
	for (i = 0; i < N_PERF_MSGS; i++)
		cds_list_add(&msgxmitarray[i].l, &d);
	while (!cds_list_empty(&d)) {
		p = d.prev;
		cds_list_del(p);
	}
	stoptime = get_microseconds();
	printf("starttime=%lld, endtime=%lld, delta=%lld us\n",
	       starttime, stoptime, stoptime - starttime);
}

#ifdef DEQ_AND_PDEQ
struct deq_test_1 {
	struct deq *d;
	int nelem;
	atomic_t *count;
	int *goflag;
	long long endtime;
};

void *deq_perf_pop(void *arg)
{
	struct deq_test_1 *t = (struct deq_test_1 *)arg;
	int i = 0;
	int me;
	struct cds_list_head *p;

	me = atomic_add_return(1, t->count) + 1;
	run_on(me);
	while (*t->goflag == GOFLAG_INIT)
		barrier();
	while (*t->goflag == GOFLAG_START) {
		if (i == t->nelem)
			break;
		p = deq_pop_r(t->d);
		if (p == NULL)
			continue;
		i++;
	}
	t->endtime = get_microseconds();
	return (void *)(long)i;
}

void deq_perf(void)
{
	struct deq d;
	struct deq_test_1 dt;
	atomic_t count;
	int goflag;
	int i;
	long long starttime;

	printf("Push %d elements through a deq\n", N_PERF_MSGS);
	init_deq(&d);
	atomic_set(&count, 0);
	dt.d = &d;
	dt.nelem = N_PERF_MSGS;
	dt.count = &count;
	dt.goflag = &goflag;

	goflag = GOFLAG_INIT;
	create_thread(deq_perf_pop, (void *)&dt);
	while (atomic_read(&count) < 1)
		barrier();
	starttime = get_microseconds();
	for (i = 0; i < N_PERF_HEADSTART; i++)
		deq_push_l(&msgxmitarray[i].l, &d);
	goflag = GOFLAG_START;
	for (; i < N_PERF_MSGS; i++)
		deq_push_l(&msgxmitarray[i].l, &d);
	wait_all_threads();
	printf("starttime=%lld, endtime=%lld, delta=%lld us\n",
	       starttime, dt.endtime, dt.endtime - starttime);
}
#endif /* #ifdef DEQ_AND_PDEQ */

void pdeq_perf(void)
{
	atomic_t count;
	struct pdeq d;
	struct deq_test dt;
	int goflag;
	int i;
	long long starttime;

	atomic_set(&count, 0);
	printf("Push %d elements through a pdeq\n", N_PERF_MSGS);
	init_pdeq(&d);
	INIT_DEQUEUE(dt, pdeq_pop_r, msgrecvarray);
	goflag = GOFLAG_INIT;
	create_thread(concurrent_ppop, (void *)&dt);
	while (atomic_read(&count) < 1)
		barrier();
	starttime = get_microseconds();
	for (i = 0; i < N_PERF_HEADSTART; i++)
		pdeq_push_l(&msgxmitarray[i].l, &d);
	goflag = GOFLAG_START;
	for (; i < N_PERF_MSGS; i++)
		pdeq_push_l(&msgxmitarray[i].l, &d);
	wait_all_threads();
	printf("starttime=%lld, endtime=%lld, delta=%lld us\n",
	       starttime, dt.endtime, dt.endtime - starttime);
}

int getdata(struct cds_list_head *p)
{
	if (p == NULL)
		return 0;
	return cds_list_entry(p, struct deq_elem, l)->data;
}

int main(int argc, char *argv[])
{
	int d1, d2, d3, d4;
	struct deq_elem e1, e2, e3;
	int i;
	struct pdeq deq;

	init_pdeq(&deq);
	printf("Empty deque: L: %p, R: %p\n",
	       pdeq_pop_l(&deq), pdeq_pop_r(&deq));

	e1.data = 1;
	e2.data = 2;
	e3.data = 3;
	pdeq_push_l(&e1.l, &deq);
	pdeq_push_l(&e2.l, &deq);
	pdeq_push_l(&e3.l, &deq);
	d1 = getdata(pdeq_pop_l(&deq));
	d2 = getdata(pdeq_pop_l(&deq));
	d3 = getdata(pdeq_pop_l(&deq));
	d4 = getdata(pdeq_pop_l(&deq));
	printf("Enqueue L, pop L: %d %d %d %d\n", d1, d2, d3, d4);

	pdeq_push_l(&e3.l, &deq);
	pdeq_push_l(&e2.l, &deq);
	pdeq_push_l(&e1.l, &deq);
	d1 = getdata(pdeq_pop_r(&deq));
	d2 = getdata(pdeq_pop_r(&deq));
	d3 = getdata(pdeq_pop_r(&deq));
	d4 = getdata(pdeq_pop_r(&deq));
	printf("Enqueue L, pop R: %d %d %d %d\n", d1, d2, d3, d4);


	pdeq_push_r(&e3.l, &deq);
	pdeq_push_r(&e2.l, &deq);
	pdeq_push_r(&e1.l, &deq);
	d1 = getdata(pdeq_pop_l(&deq));
	d2 = getdata(pdeq_pop_l(&deq));
	d3 = getdata(pdeq_pop_l(&deq));
	d4 = getdata(pdeq_pop_l(&deq));
	printf("Enqueue R, pop L: %d %d %d %d\n", d1, d2, d3, d4);

	e1.data = 1;
	e2.data = 2;
	e3.data = 3;
	pdeq_push_r(&e1.l, &deq);
	pdeq_push_r(&e2.l, &deq);
	pdeq_push_r(&e3.l, &deq);
	d1 = getdata(pdeq_pop_r(&deq));
	d2 = getdata(pdeq_pop_r(&deq));
	d3 = getdata(pdeq_pop_r(&deq));
	d4 = getdata(pdeq_pop_r(&deq));
	printf("Enqueue R, pop R: %d %d %d %d\n", d1, d2, d3, d4);

	conc_enq_l();
	conc_enq_r();
	conc_push_l();
	conc_push_r();
	melee();

	run_on(0);
	simple_deq_perf();
#ifdef DEQ_AND_PDEQ
	deq_perf();
#endif /* #ifdef DEQ_AND_PDEQ */
	for (i = 0; i < 10; i++) {
		pdeq_perf();
	}
	return 0;
}
