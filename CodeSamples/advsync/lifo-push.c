// Copyright Facebook, 2019
// Authors: Paul E. McKenney
//	Adapted from Maged Michael's pseudocode in WG14 N2369.

#include "../api.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

typedef char *value_t;

//\begin{snippet}[labelbase=ln:advsync:lifo_push:whole,commandchars=\%\@\$]
struct node_t {					//\lnlbl{struct:b}
	value_t val;
	struct node_t *next;
};						//\lnlbl{struct:e}

// LIFO list structure
struct node_t* top;				//\lnlbl{top}

void list_push(value_t v)			//\lnlbl{push:b}
{
	struct node_t *newnode = malloc(sizeof(*newnode));
	struct node_t *oldtop;

	newnode->val = v;
	oldtop = READ_ONCE(top);
	do {
		newnode->next = oldtop;
		oldtop = cmpxchg(&top, newnode->next, newnode);
	} while (newnode->next != oldtop);
}						//\lnlbl{push:e}


void list_pop_all(void (foo)(struct node_t *p))	//\lnlbl{popall:b}
{
	struct node_t *p = xchg(&top, NULL);

	while (p) {
		struct node_t *next = p->next;

		foo(p);
		free(p);
		p = next;
	}
}						//\lnlbl{popall:e}
//\end{snippet}

#define rcu_register_thread() do { } while (0)
#define rcu_unregister_thread() do { } while (0)
#include "lifo-stress.h"
