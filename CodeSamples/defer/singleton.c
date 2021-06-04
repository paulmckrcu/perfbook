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

struct myconfig {
	int a;
	int b;
} *curconfig;

int get_config(int *cur_a, int *cur_b)
{
	struct myconfig *mcp;

	rcu_read_lock();
	mcp = rcu_dereference(curconfig);
	if (!mcp) {
		rcu_read_unlock();
		return 0;
	}
	*cur_a = mcp->a;
	*cur_b = mcp->b;
	rcu_read_unlock();
	return 1;
}

void set_config(int cur_a, int cur_b)
{
	struct myconfig *mcp;

	mcp = malloc(sizeof(*mcp));
	BUG_ON(!mcp);
	mcp->a = cur_a;
	mcp->b = cur_b;
	mcp = xchg(&curconfig, mcp);
	if (mcp) {
		synchronize_rcu();
		free(mcp);
	}
}

void clear_config(void)
{
	struct myconfig *mcp;

	mcp = xchg(&curconfig, NULL);
	synchronize_rcu();
	if (mcp) {
		synchronize_rcu();
		free(mcp);
	}
}

int main(int argc, char *argv[])
{
	int a;
	int b;

	BUG_ON(get_config(&a, &b));
	clear_config();
	set_config(4, 16);
	BUG_ON(!get_config(&a, &b));
	BUG_ON(a != 4 || b != 16);
	clear_config();
	BUG_ON(get_config(&a, &b));
	return 0;
}
