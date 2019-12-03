/*
 * q.c: Simple queue with lock-free enqueue and dequeue.
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
 * Copyright (c) 2010-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include "q.h"

struct queue q = { &q.dummy, &q.dummy.next, };

void init_q(struct queue *qp)
{
	qp->head = &qp->dummy;
	qp->tail = &qp->dummy.next;
	qp->dummy.next = NULL;
}

int q_push(struct el *p, struct queue *q)
{
	struct el **oldtail;

	p->next = NULL;
	oldtail = xchg(&q->tail, p);
	*oldtail = p;
	return 1;
}

struct el *q_pop(struct queue *q)
{
	struct el *p;
	struct el *pnext;

	for (;;) {
		do {
			p = q->head;
			pnext = p->next;
			if (pnext == NULL)
				return NULL;
		} while (cmpxchg(&q->head, p, pnext) != p);
		if (p != &q->dummy)
			return p;
		q_push(&q->dummy, q);
		if (q->head == &q->dummy)
			return NULL;
	}
}

#ifdef TEST
#include "queuetorture.h"
#endif /* #ifdef TEST */
