/*
 * singleq.c: Simple queue with single-element capacity.  Allows multiple
 *	concurrent enqueues and dequeues.
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
#include "singleq.h"

struct queue q;

void init_q(struct queue *qp)
{
	qp->head = NULL;
}

int q_push(struct el *ep, struct queue *qp)
{
	return cmpxchg(&qp->head, NULL, ep) == NULL;
}

struct el *q_pop(struct queue *qp)
{
	return xchg(&qp->head, NULL);
}

#ifdef TEST
#define QUEUETORTURE_LIMITED
#include "queuetorture.h"
#endif /* #ifdef TEST */
