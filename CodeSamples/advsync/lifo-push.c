// Copyright Facebook, 2019
// Authors: Paul E. McKenney
//	Adapted from Maged Michael's pseudocode in WG14 N2369.

#include "../api.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

typedef char *value_t;

struct node_t {
	value_t val;
	struct node_t *next;
};

void set_value(struct node_t *p, value_t v)
{
	p->val = v;
}

void foo(struct node_t *p);

// LIFO list structure
struct node_t* top;

void list_push(value_t v)
{
	struct node_t *newnode = (struct node_t *) malloc(sizeof(*newnode));
	struct node_t *oldtop;

	set_value(newnode, v);
	oldtop = READ_ONCE(top);
	do {
		newnode->next = oldtop;
		oldtop = cmpxchg(&top, newnode->next, newnode);
	} while (newnode->next != oldtop);
}


void list_pop_all()
{
	struct node_t *p = xchg(&top, NULL);

	while (p) {
		struct node_t *next = p->next;

		foo(p);
		free(p);
		p = next;
	}
}

#define rcu_register_thread() do { } while (0)
#define rcu_unregister_thread() do { } while (0)
#include "lifo-stress.h"
