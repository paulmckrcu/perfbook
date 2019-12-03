/*
 * bug_srcu_a.c: simple user-level demonstration of SRCU usage bug
 *
 * Usage:
 *	./bug_srcu_a
 *		Show existence of the bug.
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
 * Copyright (c) 2011-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include "srcu.c"

#define kmalloc(s, t) malloc(s)
#define kfree(p) free(p)

struct foo {
	struct list_head list;
	int key;
	int data;
	int debug_state;
};

LIST_HEAD(mylist);
DEFINE_SPINLOCK(mylock);
struct srcu_struct mysrcu;

void do_something_with(struct foo *p)
{
}

void malicious_delay(struct foo *p)
{
	poll(NULL, 0, 10);
	if (p->debug_state)
		printf(&@@@
}

void process(void)
{
	int i1, i2;
	struct foo *p;

	i1 = srcu_read_lock(&mysrcu);
	list_for_each_entry_rcu(p, &mylist, list) {
		do_something_with(p);
		i2 = srcu_read_lock(&mysrcu);
		srcu_read_unlock(&mysrcu, i1);
		i1 = i2;
	}
	srcu_read_unlock(&mysrcu, i1);
}

int insert(int key, int data)
{
	struct foo *p = kmalloc(sizeof(*p), GFP_KERNEL);

	if (p == NULL)
		return -ENOMEM;
	p->key = key;
	p->data = data;
	p->debug_state = 0;
	spin_lock(&mylock);
	list_add_rcu(&p->list, &mylist);
	spin_unlock(&mylock);
}

int delete(int key)
{
	struct foo *p;

	spin_lock(&mylock);
	list_for_each_entry(p, &mylist, list)
		if (p->key == key) {
			list_del_rcu(&p->list);
			spin_unlock(&mylock);
			synchronize_rcu();
			p->debug_state = 1;
			kfree(p);
			return 0;
		}
	spin_unlock(&mylock);
	return -ENOENT;
}

void dumplist(void)
{
#if 0
	int data;
	int key;
	int result;

	printf("list state: ");
	for (key = 0; key < 3; key++) {
		data = -1;
		result = search(key, &data);
		printf("%d:%d(%d) ", key, data, result);
	}
#endif /* #if 0 */
}

int main(int argc, char *argv[])
{
	dumplist();
	printf("insert(0, 0);\n");
	insert(0, 0);
	dumplist();
	printf("insert(1, 1);\n");
	insert(1, 1);
	dumplist();
	printf("insert(2, 4);\n");
	insert(2, 4);
	dumplist();
	printf("delete(2) = %d; ", delete(2));
	dumplist();
}
