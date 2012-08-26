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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2010 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"

DEFINE_PER_THREAD(unsigned long, counter);
unsigned long global_count;
int stopflag;

void inc_count(void)
{
	ACCESS_ONCE(__get_thread_var(counter))++;
}

unsigned long read_count(void)
{
	return global_count;
}

void *eventual(void *arg)
{
	int t;
	int sum;

	while (stopflag < 3) {
		sum = 0;
		for_each_thread(t)
			sum += per_thread(counter, t);
		ACCESS_ONCE(global_count) = sum;
		poll(NULL, 0, 1);
		if (stopflag) {
			smp_mb();
			stopflag++;
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
	stopflag = 1;
	while (stopflag < 3)
		poll(NULL, 0, 1);
	smp_mb();
}

#include "counttorture.h"
