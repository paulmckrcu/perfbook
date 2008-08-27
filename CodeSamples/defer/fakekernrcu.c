/*
 * rcu.c: simple user-level implementation of RCU, emulating Linux kernel
 * RCU APIs.
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
#include "fakekernrcu.h"

struct rcu_data {
	spinlock_t mutex;
	struct rcu_head *nextlist;
	struct rcu_head *nexttail;
	struct rcu_head *waitlist;
	struct rcu_head *waittail;
} rcu_data;

void *call_rcu_daemon(void *arg)
{
	int i;
	struct rcu_head *list;
	struct rcu_head *next;

	for (;;) {
		for (i = 0; i < 1000; i++) {
			synchronize_rcu();
			spin_lock(&rcu_data.mutex);
			list = rcu_data.waitlist;
			if (rcu_data.nextlist == NULL) {
				rcu_data.waitlist = NULL;
				rcu_data.waittail = &rcu_data.waitlist;
			} else {
				rcu_data.waitlist = rcu_data.nextlist;
				rcu_data.waittail = rcu_data.nexttail;
			}
			rcu_data.nextlist = NULL;
			rcu_data.nexttail = &rcu_data.nextlist;
			spin_unlock(&rcu_data.mutex);
			while (list) {
				next = list->next;
				list->func(list);
				list = next;
			}
		}
		poll(NULL, 0, 1);
	}
}

void call_rcu(struct rcu_head *head, void (*func)(struct rcu_head *head))
{
	head->func = func;
	head->next = NULL;
	spin_lock(&rcu_data.mutex);
	*rcu_data.nexttail = head;
	rcu_data.nexttail = &head->next;
	spin_unlock(&rcu_data.mutex);
}

void fake_kern_rcu_init(void)
{
	smp_init();
	rcu_init();
	spin_lock_init(&rcu_data.mutex);
	rcu_data.nextlist = NULL;
	rcu_data.nexttail = &rcu_data.nextlist;
	rcu_data.waitlist = NULL;
	rcu_data.waittail = &rcu_data.waitlist;
	create_thread(call_rcu_daemon, NULL);
}
