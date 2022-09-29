/*
 * locked_list.c: Recursive tree iterator
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
 * Copyright (c) 2022 Elad Lahav
 */

#include "../api.h"

#define MAX_CHILDREN 10

struct node {
    int data;
	int nchildren;
	struct node *children[MAX_CHILDREN];
};

struct tree {
	spinlock_t s;
	struct node *root;
};

//\begin{snippet}[labelbase=ln:locking:rec_tree_iterator:tree_for_each,commandchars=\\\@\$]
void tree_for_each_rec(struct tree *tr, struct node *nd,
					   void (*callback)(struct node *))
{
	spin_unlock(&tr->s);
	callback(nd);
	spin_lock(&tr->s);

	for (int i = 0; i < nd->nchildren; i++) {
		tree_for_each_rec(tr, nd->children[i], callback);
	}
}

void tree_for_each(struct tree *tr,
				   void (*callback)(struct node *))
{
	spin_lock(&tr->s);
	tree_for_each_rec(tr, tr->root, callback);
	spin_unlock(&tr->s);
}
//\end{snippet}

void print_node_data(struct node *nd)
{
    printf("%d\n", nd->data);
}

int main(int argc, char *argv[])
{
    struct tree tr;
    struct node *nodes = calloc(sizeof(struct node), 10);

    for (int i = 0; i < 10; i++) {
        nodes[i].data = 100 + i;
    }

	spin_lock_init(&tr.s);

    tr.root = &nodes[0];

    nodes[0].nchildren = 3;
    nodes[0].children[0] = &nodes[1];
    nodes[0].children[1] = &nodes[2];
    nodes[0].children[2] = &nodes[3];

    nodes[1].nchildren = 2;
    nodes[1].children[0] = &nodes[4];
    nodes[1].children[1] = &nodes[5];

    nodes[2].nchildren = 1;
    nodes[2].children[0] = &nodes[6];

    nodes[5].nchildren = 3;
    nodes[5].children[0] = &nodes[7];
    nodes[5].children[1] = &nodes[8];
    nodes[5].children[2] = &nodes[9];

    tree_for_each(&tr, print_node_data);

	return 0;
}
