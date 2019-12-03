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
 * Copyright (c) 2010-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

//\begin{snippet}[labelbase=ln:count:count_stat_eventual:whole,commandchars=\$\[\]]
DEFINE_PER_THREAD(unsigned long, counter);		//\lnlbl{per_thr_cnt}
unsigned long global_count;				//\lnlbl{glb_cnt}
int stopflag;						//\lnlbl{stopflag}

static __inline__ void inc_count(void)			//\lnlbl{inc:b}
{
	unsigned long *p_counter = &__get_thread_var(counter);

	WRITE_ONCE(*p_counter, *p_counter + 1);
}							//\lnlbl{inc:e}

static __inline__ unsigned long read_count(void)	//\lnlbl{read:b}
{
	return READ_ONCE(global_count);
}							//\lnlbl{read:e}

void *eventual(void *arg)				//\lnlbl{eventual:b}
{
	int t;						//\lnlbl{t}
	unsigned long sum;				//\lnlbl{sum}

	while (READ_ONCE(stopflag) < 3) {
		sum = 0;
		for_each_thread(t)
			sum += READ_ONCE(per_thread(counter, t));
		WRITE_ONCE(global_count, sum);
		poll(NULL, 0, 1);
		if (READ_ONCE(stopflag)) {
			smp_mb();
			WRITE_ONCE(stopflag, stopflag + 1);
		}
	}
	return NULL;
}							//\lnlbl{eventual:e}

void count_init(void)					//\lnlbl{init:b}
{
	int en;
	thread_id_t tid;

	en = pthread_create(&tid, NULL, eventual, NULL);
	if (en != 0) {
		fprintf(stderr, "pthread_create: %s\n", strerror(en));
		exit(EXIT_FAILURE);
	}
}							//\lnlbl{init:e}

void count_cleanup(void)				//\lnlbl{cleanup:b}
{
	WRITE_ONCE(stopflag, 1);
	while (READ_ONCE(stopflag) < 3)
		poll(NULL, 0, 1);
	smp_mb();
}							//\lnlbl{cleanup:e}
//\end{snippet}

#include "counttorture.h"
