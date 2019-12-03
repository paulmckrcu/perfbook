/*
 * existence_test.c: Test existence data structures.
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

#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "../../api.h"
#include "existence.h"
#define _GNU_SOURCE
#define _LGPL_SOURCE
#define RCU_SIGNAL
#include <urcu.h>

struct existence *outgoing;
struct existence *incoming;
struct existence_group *egp;

static void *scan_existence(void *arg)
{
	int i = 0;

	for (;;) {
		if (!existence_exists(&outgoing)) {
			BUG_ON(!existence_exists(&incoming));
			break;
		}
		if (existence_exists(&incoming)) {
			BUG_ON(existence_exists(&outgoing));
			break;
		}
		i++;
	}
	/* printf("scan_existence(): %d loops\n", i); */
	return NULL;
}

void do_one(void)
{
	thread_id_t tid;

	egp = existence_alloc();
	BUG_ON(!egp);

	BUG_ON(existence_is_changing(&outgoing));
	BUG_ON(!existence_exists(&outgoing));
	existence_set(&outgoing, existence_get_outgoing(egp));
	BUG_ON(!existence_is_changing(&outgoing));
	BUG_ON(!existence_is_outgoing(&outgoing));
	BUG_ON(existence_is_incoming(&outgoing));
	BUG_ON(!existence_exists(&outgoing));

	BUG_ON(existence_is_changing(&incoming));
	BUG_ON(!existence_exists(&incoming));
	existence_set(&incoming, existence_get_incoming(egp));
	BUG_ON(!existence_is_changing(&incoming));
	BUG_ON(existence_is_outgoing(&incoming));
	BUG_ON(!existence_is_incoming(&incoming));
	BUG_ON(existence_exists(&incoming));

	tid = create_thread(scan_existence, NULL);

	poll(NULL, 0, 1);

	existence_switch(egp);

	BUG_ON(existence_exists(&outgoing));
	BUG_ON(!existence_is_outgoing(&outgoing));
	BUG_ON(existence_is_incoming(&outgoing));

	BUG_ON(!existence_exists(&incoming));
	BUG_ON(existence_is_outgoing(&incoming));
	BUG_ON(!existence_is_incoming(&incoming));

	(void)wait_thread(tid);

	existence_clear(&outgoing);
	BUG_ON(existence_is_changing(&outgoing));
	BUG_ON(!existence_exists(&outgoing));

	existence_clear(&incoming);
	BUG_ON(existence_is_changing(&incoming));
	BUG_ON(!existence_exists(&incoming));

	existence_free(egp);
	egp = NULL;
}

int main(int argc, char *argv[])
{
	int i;

	for (i = 0; i < 1000; i++)
		do_one();
	return 0;
}
