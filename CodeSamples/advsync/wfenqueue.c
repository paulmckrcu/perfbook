/*
 * wfenqueue.c: Simple queue with wait-free enqueue and blocking dequeue.
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
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include "q.h"

void init_q(struct queue *qp)
{
	qp->head = &qp->dummy;
	qp->tail = &qp->dummy.next;
	qp->dummy.next = NULL;
	spin_lock_init(&qp->mutex);
}

int q_push(struct el *ep, struct queue *qp)
{
	struct el **tail;

	ep->next = NULL;
	tail = xchg(&qp->tail, ep);
	*tail = ep;
	return 1;
}

struct el *__q_pop(struct queue *qp)
{
	struct el *ep;

	if (qp->head == &qp->dummy && qp->tail == &qp->dummy.next)
		return NULL;
	ep = qp->head;
	while (ep->next == NULL) {
		poll(NULL, 0, 1);
	}
	qp->head = ep->next;
	if (ep == &qp->dummy) {
		q_push(ep, qp);
		return __q_pop(qp);
	}
	return ep;
}

struct el *q_pop(struct queue *qp)
{
	struct el *ep;

	spin_lock(&qp->mutex);
	ep = __q_pop(qp);
	spin_unlock(&qp->mutex);
	return ep;
}

#ifdef TEST
#include "queuetorture.h"
#endif /* #ifdef TEST */
