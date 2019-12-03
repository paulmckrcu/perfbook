/*
 * tree.h: Search tree supporting atomic move.
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
 * Copyright (c) 2014-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#ifndef _TREE_H
#define _TREE_H

#define _GNU_SOURCE
#define _LGPL_SOURCE
#define RCU_SIGNAL
#include <urcu.h>
#include "existence.h"

/*
 * Structure for internal and leaf nodes.  Data is stored separately,
 * linked via the ->data field.
 */
struct treenode {
	int key;
	char perm;
	char deleted;
	struct treenode *lc;
	struct treenode *rc;
	void *data; /* NULL for non-leaf nodes. */
	struct existence *existence;
	spinlock_t lock;
	struct rcu_head rh;
};

/*
 * Root of a tree.
 */
struct treeroot {
	struct treenode min;
	struct treenode max;
} __attribute__((__aligned__(CACHE_LINE_SIZE)));

void treenode_wire_call_rcu(void);
struct treeroot *tree_alloc(void);
void tree_free(struct treeroot *trp, void (*freefunc)(void *p));
void *tree_lookup(struct treeroot *trp, int key, void (*func)(void *data));
void *tree_lookup_relaxed(struct treeroot *trp, int key);
int tree_insert_existence(struct treeroot *trp, int key, void *data,
			   struct existence *node_existence, int wait);
int tree_insert(struct treeroot *trp, int key, void *data);
int tree_atomic_move(struct treeroot *srcp, struct treeroot *dstp,
		     int key, void **data);
void treenode_cache_stats(long *nftc, long *natc, long *nmt, long *tcc);

#endif /* #ifndef _TREE_H */
