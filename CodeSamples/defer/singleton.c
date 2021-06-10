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
#include "../lib/random.h"

#include "../api.h"

//\begin{snippet}[labelbase=ln:defer:singleton:get,commandchars=\\\[\]]
struct myconfig {					//\lnlbl{myconfig.b}
	int a;
	int b;
} *curconfig;						//\lnlbl{myconfig.e}

int get_config(int *cur_a, int *cur_b)			//\lnlbl{get_config.b}
{
	struct myconfig *mcp;

	rcu_read_lock();				//\lnlbl{rrl}
	mcp = rcu_dereference(curconfig);		//\lnlbl{rderef}
	if (!mcp) {					//\lnlbl{nullchk}
		rcu_read_unlock();			//\lnlbl{rrul1}
		return 0;				//\lnlbl{retfail}
	}
	*cur_a = mcp->a;				//\lnlbl{copya}
	*cur_b = mcp->b;				//\lnlbl{copyb}
	rcu_read_unlock();				//\lnlbl{rrul2}
	return 1;					//\lnlbl{retsuccess}
}							//\lnlbl{get_config.e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:defer:singleton:set,commandchars=\\\[\]]
void set_config(int cur_a, int cur_b)			//\lnlbl{set_config.b}
{
	struct myconfig *mcp;

	mcp = malloc(sizeof(*mcp));			//\lnlbl{allocinit.b}
	BUG_ON(!mcp);
	mcp->a = cur_a;
	mcp->b = cur_b;					//\lnlbl{allocinit.e}
	mcp = xchg(&curconfig, mcp);			//\lnlbl{xchg}
	if (mcp) {					//\lnlbl{if}
		synchronize_rcu();			//\lnlbl{sr}
		free(mcp);				//\lnlbl{free}
	}
}							//\lnlbl{set_config.e}
//\end{snippet}

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

volatile int goflag = 1;

void *singleton_reader(void *arg)
{
	int a;
	int b;

	rcu_register_thread();
	while (READ_ONCE(goflag)) {
		if (get_config(&a, &b))
			BUG_ON(a * a != b);
	}
	rcu_unregister_thread();
	return NULL;
}

void *singleton_updater(void *arg)
{
	int a;
	int b;

	while (READ_ONCE(goflag)) {
		a = random() & 0xff;
		b = a * a;
		set_config(a, b);
	}
	return NULL;
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

	set_config(5, 25);
	create_thread(singleton_reader, NULL);
	create_thread(singleton_reader, NULL);
	create_thread(singleton_updater, NULL);
	sleep(10);
	WRITE_ONCE(goflag, 0);
	wait_all_threads();
	if (get_config(&a, &b))
		clear_config();
	return 0;
}
