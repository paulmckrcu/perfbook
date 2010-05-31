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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2010 Paul E. McKenney, IBM Corporation.
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
