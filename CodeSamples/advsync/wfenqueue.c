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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"
#include "wfenqueue.h"

void wfenqueue_init(struct wfenqueue *wp)
{
	wp->head = &wp->dummy;
	wp->tail = &wp->dummy.next;
	wp->dummy.next = NULL;
	spin_lock_init(&wp->mutex);
}

void wfenqueue_enq(struct wfenqueue_elem *ep, struct wfenqueue *wp)
{
	struct wfenqueue_elem **tail;

	ep->next = NULL;
	tail = xchg(&wp->tail, ep);
	*tail = ep;
}

struct wfenqueue_elem *__wfenqueue_deq(struct wfenqueue *wp)
{
	struct wfenqueue_elem *ep;

	if (wp->head == &wp->dummy && wp->tail == &wp->dummy.next)
		return NULL;
	ep = wp->head;
	while (ep->next == NULL) {
		poll(NULL, 0, 1);
	}
	wp->head = ep->next;
	if (ep == &wp->dummy) {
		wfenqueue_enq(ep, wp);
		return __wfenqueue_deq(wp);
	}
	return ep;
}

struct wfenqueue_elem *wfenqueue_deq(struct wfenqueue *wp)
{
	struct wfenqueue_elem *ep;

	spin_lock(&wp->mutex);
	ep = __wfenqueue_deq(wp);
	spin_unlock(&wp->mutex);
	return ep;
}

#ifdef TEST
int main(int argc, char *argv[])
{
	struct wfenqueue wq;
	struct wfenqueue_elem e1;
	struct wfenqueue_elem e2;
	struct wfenqueue_elem *ep;

	wfenqueue_init(&wq);
	printf("enqueuing %p\n", &e1);
	wfenqueue_enq(&e1, &wq);
	printf("enqueuing %p\n", &e2);
	wfenqueue_enq(&e2, &wq);
	ep = wfenqueue_deq(&wq);
	printf("dequeued %p\n", ep);
	ep = wfenqueue_deq(&wq);
	printf("dequeued %p\n", ep);
	return 0;
}
#endif /* #ifdef TEST */
