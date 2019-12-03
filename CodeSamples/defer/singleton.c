/*
 * singleton.c: Trivial singleton data structure protected by RCU.
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
 * Copyright (c) 2019-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#define _GNU_SOURCE
#define _LGPL_SOURCE

#ifndef DO_QSBR
#define RCU_SIGNAL
#include <urcu.h>
#else /* #ifndef DO_QSBR */
#include <urcu-qsbr.h>
#endif /* #else #ifndef DO_QSBR */

#include "../api.h"

struct foo {
	int data;
} *gptr = NULL;

int lookup(int *dp)
{
	struct foo *p;

	rcu_read_lock();
	p = rcu_dereference(gptr);
	if (!p) {
		rcu_read_unlock();
		return 0;
	}
	*dp = p->data;
	rcu_read_unlock();
	return 1;
}

int insert(int newdata)
{
	struct foo *p;

	p = malloc(sizeof(*p));
	BUG_ON(!p);
	p->data = newdata;
	if (cmpxchg(&gptr, NULL, p)) {
		free(p);
		return 0;
	}
	return 1;
}

int uninsert(void)
{
	struct foo *p;

	p = xchg(&gptr, NULL);
	synchronize_rcu();
	free(p);
	return !!p;
}

int main(int argc, char *argv[])
{
	int d;

	BUG_ON(lookup(&d));
	BUG_ON(uninsert());
	BUG_ON(!insert(42));
	BUG_ON(!lookup(&d));
	BUG_ON(d != 42);
	BUG_ON(!uninsert());
	BUG_ON(lookup(&d));
	return 0;
}
