/*
 * queuetorture.h: torture tests for simple queue.
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

#define GOFLAG_INIT	0
#define GOFLAG_START	1
#define GOFLAG_STOP	2

struct q_test {
	int (*push)(struct el *e, struct queue *q);
	struct el *(*pop)(struct queue *q);
	struct queue *q;
	struct el *p;
	struct el **ql;
	int nelem;
	int datastart;
	int datainc;
	atomic_t *count;
	int *goflag;
	long long endtime;
};

int q_push_error(struct el *e, struct queue *q)
{
	printf("q_push_error()\n");
	abort();
}

struct el *q_pop_error(struct queue *q)
{
	printf("q_pop_error()\n");
	abort();
}

/*
 * Enqueue elements as specified by the deq_test structure.  This may
 * either be called directly (with the specified goflag already set
 * to GOFLAG_START) or via create_thread().
 */
void *concurrent_push(void *arg)
{
	struct q_test *t = (struct q_test *)arg;
	int i;
	int me;
	struct el *p = t->p;
	int v = t->datastart;

	me = atomic_add_return(1, t->count) + 1;
	run_on(me);
	while (*t->goflag == GOFLAG_INIT)
		barrier();

	for (i = 0; i < t->nelem; i++) {
		p[i].data = v;
		while (!t->push(&p[i], t->q))
			continue;
		v += t->datainc;
	}
	return (NULL);
}

/*
 * Dequeue as specified by the q_test structure. This may be called
 * directly (in which case the number of elements to be popped must
 * be exactly that required and the specified goflag already set to
 * GOFLAG_START), or via create_thread().
 */
void *concurrent_pop(void *arg)
{
	struct q_test *t = (struct q_test *)arg;
	int i, j;
	int me;
	struct el *p;

	me = atomic_add_return(1, t->count) + 1;
	run_on(me);
	while (*t->goflag == GOFLAG_INIT)
		barrier();

	i = 0;
	while (*t->goflag == GOFLAG_START) {
		if (i == t->nelem)
			break;
		p = t->pop(t->q);
		if (p == NULL)
			continue;
		t->ql[i++] = p;
	}
	t->endtime = get_microseconds();
	for (j = i; j < 2 * N_TEST_ELEMS; j++)
		t->ql[j] = NULL;
	return (void *)(long)i;
}

/*
 * Variable declarations required for the queue tests.
 */
#define QTEST_VAR_DEFS() \
	atomic_t count; \
	struct queue q; \
	struct q_test qtpush1; \
	struct q_test qtpush2; \
	struct q_test qtpop1; \
	struct q_test __maybe_unused qtpop2; \
	struct el qtelem1[N_TEST_ELEMS]; \
	struct el qtelem2[N_TEST_ELEMS]; \
	struct el *qtelempop1[2 * N_TEST_ELEMS]; \
	struct el __maybe_unused *qtelempop2[2 * N_TEST_ELEMS]; \
	int goflag


/*
 * Initialize a q_test structure for pushing.
 * The caller must provide a struct queue named "q", an atomic_t named
 * "count", and an int named "goflag".
 */
#define INIT_PUSH(qt, f, ea, start, inc) \
do { \
	qt.push = &f; \
	qt.pop = &q_pop_error; \
	qt.q = &q; \
	qt.p = ea; \
	qt.nelem = sizeof(ea) / sizeof(ea[0]); \
	qt.datastart = start; \
	qt.datainc = inc; \
	qt.count = &count; \
	qt.goflag = &goflag; \
} while (0)

/*
 * Initialize a q_test structure for popping.
 * The caller must provide a struct queue named "q", an atomic_t named
 * "count", and an int named "goflag".
 */
#define INIT_POP(qt, f, ea) \
do { \
	qt.push = &q_push_error; \
	qt.pop = f; \
	qt.q = &q; \
	qt.ql = ea; \
	qt.nelem = sizeof(ea) / sizeof(ea[0]); \
	qt.count = &count; \
	qt.goflag = &goflag; \
} while (0)

/*
 * Initialize a q_test structure for enqueuing.
 * The caller must provide a struct queue named "q", an atomic_t named
 * "count", and an int named "goflag".
 */
#define INIT_QUEUE(qt, f, epa) \
do { \
	qt.push = &q_push_error; \
	qt.pop = &f; \
	qt.q = &q; \
	qt.ql = epa; \
	qt.nelem = sizeof(epa) / sizeof(epa[0]); \
	qt.count = &count; \
	qt.goflag = &goflag; \
} while (0)

/*
 * Run a pair of push threads on the specified q_test structures.
 * The caller must supply an atomic_t "count" and an int "goflag".
 */
#define RUN_ENQUEUE_PAIR(qte1, qte2) \
do { \
	goflag = GOFLAG_INIT; \
	atomic_set(&count, 0); \
	create_thread(concurrent_push, (void *)&qte1); \
	create_thread(concurrent_push, (void *)&qte2); \
	while (atomic_read(&count) < 2) \
		barrier(); \
	goflag = GOFLAG_START; \
	wait_all_threads(); \
} while (0)

/*
 * Check a sequence of elements removed from a queue.  These must have
 * been inserted by a pair of threads, one of which pushed positive
 * elements and the other negative, such that the first element popped
 * is either +1 or -1.
 */
#define CHECK_SEQUENCE_PAIR(qtelemdeq) \
do { \
	int i; \
	int ipos = 0; \
	int ineg = 0; \
	\
	atomic_set(&count, 0); \
	goflag = GOFLAG_START; \
	if ((i = (long)concurrent_pop(&qtpop1)) != qtpop1.nelem) { \
		printf("Expected to pop %d, got %d\n", \
		       qtpop1.nelem, i); \
		abort(); \
	} \
	\
	for (i = 0; i < sizeof(qtelemdeq) / sizeof(qtelemdeq[0]); i++) { \
		int icheck = qtelemdeq[i]->data; \
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

void conc_push(void)
{
	QTEST_VAR_DEFS();

	printf("Concurrently push 2, pop 1\n");

	init_q(&q);

	INIT_PUSH(qtpush1, q_push, qtelem1, 1, 1);
	INIT_PUSH(qtpush2, q_push, qtelem2, -1, -1);
	RUN_ENQUEUE_PAIR(qtpush1, qtpush2);

	INIT_POP(qtpop1, q_pop, qtelempop1);
	CHECK_SEQUENCE_PAIR(qtelempop1);
}

void melee(void)
{
	QTEST_VAR_DEFS();
	int i, j;
	int lastpos, lastneg;
	int ahead;
	int ok = 1;
	char check[2 * N_TEST_ELEMS + 1] = { 0 };

	printf("Concurrent melee between a pair of pushes and of pops\n");

	init_q(&q);

	INIT_PUSH(qtpush1, q_push, qtelem1, 1, 1);
	INIT_PUSH(qtpush2, q_push, qtelem2, -1, -1);
	INIT_POP(qtpop1, q_pop, qtelempop1);
	INIT_POP(qtpop2, q_pop, qtelempop2);

	goflag = GOFLAG_INIT;
	atomic_set(&count, 0);
	create_thread(concurrent_push, (void *)&qtpush1);
	create_thread(concurrent_push, (void *)&qtpush2);
	create_thread(concurrent_pop, (void *)&qtpop1);
	create_thread(concurrent_pop, (void *)&qtpop2);
	while (atomic_read(&count) < 4)
		barrier();
	goflag = GOFLAG_START;
	sleep(3);
	goflag = GOFLAG_STOP;
	wait_all_threads();

	for (i = 0; i < 2 * N_TEST_ELEMS; i++) {
		if (qtelempop1[i] != NULL) {
			printf("%d ", qtelempop1[i]->data);
			if (check[qtelempop1[i]->data + N_TEST_ELEMS] != 0)
				abort();
			check[qtelempop1[i]->data + N_TEST_ELEMS] = 1;
		}
		if (qtelempop2[i] != NULL) {
			printf("%d ", qtelempop2[i]->data);
			if (check[qtelempop2[i]->data + N_TEST_ELEMS] != 0)
				abort();
			check[qtelempop2[i]->data + N_TEST_ELEMS] = 1;
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
	lastpos = lastneg = 0;
	i = j = 0;
	while ((i < 2 * N_TEST_ELEMS && qtelempop1[i] != NULL) ||
	       (j < 2 * N_TEST_ELEMS && qtelempop2[j] != NULL)) {
		ahead = 0;
		if (i < 2 * N_TEST_ELEMS && qtelempop1[i] != NULL) {
			if (qtelempop1[i]->data == lastpos + 1) {
				lastpos++;
				ahead = 1;
				i++;
			} else if (qtelempop1[i]->data == lastneg - 1) {
				lastneg--;
				ahead = 1;
				i++;
			}
		}
		if (j < 2 * N_TEST_ELEMS && qtelempop2[j] != NULL) {
			if (qtelempop2[j]->data == lastpos + 1) {
				lastpos++;
				ahead = 1;
				j++;
			} else if (qtelempop2[j]->data == lastneg - 1) {
				lastneg--;
				ahead = 1;
				j++;
			}
		}
		if (ahead == 0)
			abort();
	}
	if (!ok)
		abort();
	printf("OK\n");
}

#define N_PERF_MSGS (1000*1000)
#define N_PERF_HEADSTART (N_PERF_MSGS / 100)

struct cds_list_head listheadxmitarray[N_PERF_MSGS];
struct el msgxmitarray[N_PERF_MSGS];
struct el *msgrecvarray[N_PERF_MSGS];

void simple_q_perf(void)
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
		cds_list_add(&listheadxmitarray[i], &d);
	while (!cds_list_empty(&d)) {
		p = d.prev;
		cds_list_del(p);
	}
	stoptime = get_microseconds();
	printf("starttime=%lld, endtime=%lld, delta=%lld us\n",
	       starttime, stoptime, stoptime - starttime);
}

void queue_perf(void)
{
	atomic_t count;
	struct queue q;
	struct q_test qt;
	int goflag;
	int i;
	long long starttime;

	atomic_set(&count, 0);
	printf("Push %d elements through a queue\n", N_PERF_MSGS);
	init_q(&q);
	INIT_QUEUE(qt, q_pop, msgrecvarray);
	goflag = GOFLAG_INIT;
	create_thread(concurrent_pop, (void *)&qt);
	while (atomic_read(&count) < 1)
		barrier();
	starttime = get_microseconds();
	for (i = 0; i < N_PERF_HEADSTART; i++)
		q_push(&msgxmitarray[i], &q);
	goflag = GOFLAG_START;
	for (; i < N_PERF_MSGS; i++)
		q_push(&msgxmitarray[i], &q);
	wait_all_threads();
	printf("starttime=%lld, endtime=%lld, delta=%lld us\n",
	       starttime, qt.endtime, qt.endtime - starttime);
}

int getdata(struct el *p)
{
	if (p == NULL)
		return 0;
	return p->data;
}

int main(int argc, char *argv[])
{
	int d1, d2, d3, d4;
	struct el e1, e2, e3;
	int __maybe_unused i;
	struct queue q;

	init_q(&q);
	printf("Pop from empty queue: %p\n", q_pop(&q));

	e1.data = 1;
	e2.data = 2;
	e3.data = 3;
	q_push(&e1, &q);
	q_push(&e2, &q);
	q_push(&e3, &q);
	d1 = getdata(q_pop(&q));
	d2 = getdata(q_pop(&q));
	d3 = getdata(q_pop(&q));
	d4 = getdata(q_pop(&q));
	printf("Push, pop: %d %d %d %d\n", d1, d2, d3, d4);

#ifndef QUEUETORTURE_LIMITED
	conc_push();
#endif /* #ifdef QUEUETORTURE_LIMITED */
	melee();

	run_on(0);
	simple_q_perf();
#ifndef QUEUETORTURE_LIMITED
	for (i = 0; i < 10; i++) {
		queue_perf();
	}
#endif /* #ifdef QUEUETORTURE_LIMITED */
	return 0;
}
