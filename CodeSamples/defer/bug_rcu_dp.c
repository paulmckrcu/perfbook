/*
 * bug_rcu_dp.c: simple user-level demonstration of early RCU bug.
 *
 * Usage:
 *	./bug_rcu_dp
 *		Show existence of the bug.
 *
 * This program will fail to compile under liburcu0 and earlier.
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
#include <urcu.h>

#define kmalloc(s, t) malloc(s)
#define kfree(p) free(p)

struct foo {
	struct cds_list_head list;
	int key;
	int data;
};

CDS_LIST_HEAD(mylist);
DEFINE_SPINLOCK(mylock);
struct foo *cache;

int search(int key, int *data)
{
	struct foo *p;

	rcu_read_lock();
	p = rcu_dereference(cache);
	if (p != NULL && p->key == key)
		goto found;
	cds_list_for_each_entry_rcu(p, &mylist, list)
		if (p->key == key) {
			rcu_assign_pointer(cache, p);
			goto found;
		}
	rcu_read_unlock();
	return -ENOENT;
found:
	*data = p->data;
	rcu_read_unlock();
	return 0;
}

int insert(int key, int data)
{
	struct foo *p = kmalloc(sizeof(*p), GFP_KERNEL);

	if (p == NULL)
		return -ENOMEM;
	p->key = key;
	p->data = data;
	spin_lock(&mylock);
	cds_list_add_rcu(&p->list, &mylist);
	spin_unlock(&mylock);
	return 0;
}

int delete(int key)
{
	struct foo *p;

	spin_lock(&mylock);
	cds_list_for_each_entry(p, &mylist, list)
		if (p->key == key) {
			cds_list_del_rcu(&p->list);
			spin_unlock(&mylock);
			synchronize_rcu();
			kfree(p);
			return 0;
		}
	spin_unlock(&mylock);
	return -ENOENT;
}

void dumpcache(void)
{
	if (cache != NULL)
		printf("cache: %d:%d\n", cache->key, cache->data);
	else
		printf("cache empty\n");
}

void dumplist(void)
{
	int data;
	int key;
	int result;

	printf("list state: ");
	for (key = 0; key < 3; key++) {
		data = -1;
		result = search(key, &data);
		printf("%d:%d(%d) ", key, data, result);
	}
	dumpcache();
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
	dumpcache();
	dumplist();
	return 0;
}
