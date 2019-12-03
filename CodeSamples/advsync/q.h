/*
 * q.h: Simple atomic queue.
 *
 * This is similar to the enqueueing operation used in the MCS lock.
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

#ifndef _Q_H_
#define _Q_H_

struct el {
	struct el *next;
	int data;
};
struct queue {
	struct el *head;
	struct el **tail;
	struct el dummy;
	spinlock_t mutex;
};

void init_q(struct queue *qp);
int q_push(struct el *p, struct queue *q);
struct el *q_pop(struct queue *q);

#endif /* #ifndef _Q_H_ */
