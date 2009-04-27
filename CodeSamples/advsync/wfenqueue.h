/*
 * wfenqueue.h: Simple queue with wait-free enqueue and blocking dequeue.
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

#ifndef _WFENQUEUE_H_
#define _WFENQUEUE_H_

struct wfenqueue_elem {
	struct wfenqueue_elem *next;
};

struct wfenqueue {
	struct wfenqueue_elem *head;
	struct wfenqueue_elem **tail;
	struct wfenqueue_elem dummy;
	spinlock_t mutex;
};

extern void wfenqueue_init(struct wfenqueue *wp);
extern void wfenqueue_enq(struct wfenqueue_elem *ep, struct wfenqueue *wp);
extern struct wfenqueue_elem *wfenqueue_deq(struct wfenqueue *wp);

#endif /* #ifndef _WFENQUEUE_H_ */
