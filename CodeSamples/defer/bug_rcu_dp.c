/*
 * bug_rcu_dp.c: simple user-level demonstration of early RCU bug.
 *
 * Usage:
 *	./bug_rcu_dp nreaders [ nwriters [ nelems [ cpustride ] ] ]
 *		Run a performance test with the specified
 * 		number of readers and writers, running on CPUs spaced
 *		by <cpustride>.  Thus "./seqlocktorture 8 8 2" would
 *		run 8 readers and 8 writers on even-numbered CPUs from
 *		0 to 30.
 *
 * The above tests produce output as follows:
 *
 * n_reads: 824000  n_writes: 75264000  nreaders: 1  nwriters: 1 duration: 240
 * ns/read: 291.262  ns/write: 3.18878
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
 * Copyright (c) 2011 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"
#include <urcu.h>

#define kmalloc(s, t) malloc(s)
#define kfree(p) free(p)

struct foo {
	struct list_head list;
	int key;
	int data;
};

LIST_HEAD(mylist);
DEFINE_SPINLOCK(mylock);
struct foo *cache;

int search(int key, int *data)
{
	struct foo *p;

	rcu_read_lock();
	if (cache != NULL) {
		p = rcu_dereference(cache);
		if (p->key == key)
			goto found;
	}
	list_for_each_entry_rcu(p, &mylist, list)
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
}
