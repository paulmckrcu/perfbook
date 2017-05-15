/*
 * count_stat_eventual.c: Per-thread atomic statistical counters with
 *	"eventually consistent" semantics.
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
 * Copyright (c) 2010 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"

DEFINE_PER_THREAD(unsigned long, counter);
unsigned long global_count;
int stopflag;

void inc_count(void)
{
	WRITE_ONCE(__get_thread_var(counter),
		   READ_ONCE(__get_thread_var(counter)) + 1);
}

unsigned long read_count(void)
{
	return READ_ONCE(global_count);
}

void *eventual(void *arg)
{
	int t;
	unsigned long sum;

	while (READ_ONCE(stopflag) < 3) {
		sum = 0;
		for_each_thread(t)
			sum += READ_ONCE(per_thread(counter, t));
		WRITE_ONCE(global_count, sum);
		poll(NULL, 0, 1);
		if (READ_ONCE(stopflag)) {
			smp_mb();
			WRITE_ONCE(stopflag, READ_ONCE(stopflag) + 1);
		}
	}
	return NULL;
}

void count_init(void)
{
	thread_id_t tid;

	if (pthread_create(&tid, NULL, eventual, NULL) != 0) {
		perror("count_init:pthread_create");
		exit(-1);
	}
}

void count_cleanup(void)
{
	WRITE_ONCE(stopflag, 1);
	smp_mb();
	while (READ_ONCE(stopflag) < 3)
		poll(NULL, 0, 1);
	smp_mb();
}

#include "counttorture.h"
