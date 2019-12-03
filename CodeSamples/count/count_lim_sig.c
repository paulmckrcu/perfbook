/*
 * count_lim_sig.c: simple limit counter that uses POSIX signals
 *	to steal from other threads.
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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include <signal.h>

//\begin{snippet}[labelbase=ln:count:count_lim_sig:data,commandchars=\\\@\$]
#define THEFT_IDLE   0					//\lnlbl{value:b}
#define THEFT_REQ    1
#define	THEFT_ACK    2
#define THEFT_READY  3

int __thread theft = THEFT_IDLE;
int __thread counting = 0;				//\lnlbl{value:e}
unsigned long __thread counter = 0;			//\lnlbl{var:b}
unsigned long __thread countermax = 0;
unsigned long globalcountmax = 10000;
unsigned long globalcount = 0;
unsigned long globalreserve = 0;
unsigned long *counterp[NR_THREADS] = { NULL };
unsigned long *countermaxp[NR_THREADS] = { NULL };	//\lnlbl{maxp}
int *theftp[NR_THREADS] = { NULL };			//\lnlbl{theftp}
DEFINE_SPINLOCK(gblcnt_mutex);
#define MAX_COUNTERMAX 100				//\lnlbl{var:e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim_sig:migration,commandchars=\\\@\$]
static void globalize_count(void)		//\lnlbl{globalize:b}
{
	globalcount += counter;
	counter = 0;
	globalreserve -= countermax;
	countermax = 0;
}						//\lnlbl{globalize:e}

static void flush_local_count_sig(int unused)	//\lnlbl{flush_sig:b}
{
	if (READ_ONCE(theft) != THEFT_REQ)	//\lnlbl{flush_sig:check:REQ}
		return;				//\lnlbl{flush_sig:return:n}
	smp_mb();				//\lnlbl{flush_sig:mb:1}
	WRITE_ONCE(theft, THEFT_ACK);		//\lnlbl{flush_sig:set:ACK}
	if (!counting) {			//\lnlbl{flush_sig:check:fast}
		WRITE_ONCE(theft, THEFT_READY);	//\lnlbl{flush_sig:set:READY}
	}
	smp_mb();
}						//\lnlbl{flush_sig:e}

static void flush_local_count(void)			//\lnlbl{flush:b}
{
	int t;
	thread_id_t tid;

	for_each_tid(t, tid)				//\lnlbl{flush:loop:b}
		if (theftp[t] != NULL) {		//\lnlbl{flush:skip}
			if (*countermaxp[t] == 0) {	//\lnlbl{flush:checkmax}
				WRITE_ONCE(*theftp[t], THEFT_READY);//\lnlbl{flush:READY}
				continue;		//\lnlbl{flush:next}
			}
			WRITE_ONCE(*theftp[t], THEFT_REQ);//\lnlbl{flush:REQ}
			pthread_kill(tid, SIGUSR1);	//\lnlbl{flush:signal}
		}					//\lnlbl{flush:loop:e}
	for_each_tid(t, tid) {				//\lnlbl{flush:loop2:b}
		if (theftp[t] == NULL)			//\lnlbl{flush:skip:nonexist}
			continue;			//\lnlbl{flush:next2}
		while (READ_ONCE(*theftp[t]) != THEFT_READY) {//\lnlbl{flush:loop3:b}
			poll(NULL, 0, 1);		//\lnlbl{flush:block}
			if (READ_ONCE(*theftp[t]) == THEFT_REQ)//\lnlbl{flush:check:REQ}
				pthread_kill(tid, SIGUSR1);//\lnlbl{flush:signal2}
		}					//\lnlbl{flush:loop3:e}
		globalcount += *counterp[t];		//\lnlbl{flush:thiev:b}
		*counterp[t] = 0;
		globalreserve -= *countermaxp[t];
		*countermaxp[t] = 0;			//\lnlbl{flush:thiev:e}
		WRITE_ONCE(*theftp[t], THEFT_IDLE);	//\lnlbl{flush:IDLE}
	}						//\lnlbl{flush:loop2:e}
}							//\lnlbl{flush:e}

static void balance_count(void)				//\lnlbl{balance:b}
{
	countermax = globalcountmax - globalcount -
	             globalreserve;
	countermax /= num_online_threads();
	if (countermax > MAX_COUNTERMAX)
		countermax = MAX_COUNTERMAX;
	globalreserve += countermax;
	counter = countermax / 2;
	if (counter > globalcount)
		counter = globalcount;
	globalcount -= counter;
}							//\lnlbl{balance:e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim_sig:add,commandchars=\\\@\$]
int add_count(unsigned long delta)			//\lnlbl{b}
{
	int fastpath = 0;

	WRITE_ONCE(counting, 1);			//\lnlbl{fast:b}
	barrier();					//\lnlbl{barrier:1}
	if (READ_ONCE(theft) <= THEFT_REQ &&		//\lnlbl{check:b}
	    countermax - counter >= delta) {		//\lnlbl{check:e}
		WRITE_ONCE(counter, counter + delta);	//\lnlbl{add:f}
		fastpath = 1;				//\lnlbl{fasttaken}
	}
	barrier();					//\lnlbl{barrier:2}
	WRITE_ONCE(counting, 0);			//\lnlbl{clearcnt}
	barrier();					//\lnlbl{barrier:3}
	if (READ_ONCE(theft) == THEFT_ACK) {		//\lnlbl{check:ACK}
		smp_mb();				//\lnlbl{mb}
		WRITE_ONCE(theft, THEFT_READY);		//\lnlbl{READY}
	}
	if (fastpath)
		return 1;				//\lnlbl{return:fs}
	spin_lock(&gblcnt_mutex);			//\lnlbl{acquire}
	globalize_count();
	if (globalcountmax - globalcount -
	    globalreserve < delta) {
		flush_local_count();
		if (globalcountmax - globalcount -
		    globalreserve < delta) {
			spin_unlock(&gblcnt_mutex);	//\lnlbl{release:f}
			return 0;			//\lnlbl{return:sf}
		}
	}
	globalcount += delta;
	balance_count();
	spin_unlock(&gblcnt_mutex);
	return 1;					//\lnlbl{return:ss}
}							//\lnlbl{e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim_sig:sub,commandchars=\\\@\$]
int sub_count(unsigned long delta)
{
	int fastpath = 0;

	WRITE_ONCE(counting, 1);
	barrier();
	if (READ_ONCE(theft) <= THEFT_REQ &&
	    counter >= delta) {
		WRITE_ONCE(counter, counter - delta);
		fastpath = 1;
	}
	barrier();
	WRITE_ONCE(counting, 0);
	barrier();
	if (READ_ONCE(theft) == THEFT_ACK) {
		smp_mb();
		WRITE_ONCE(theft, THEFT_READY);
	}
	if (fastpath)
		return 1;
	spin_lock(&gblcnt_mutex);
	globalize_count();
	if (globalcount < delta) {
		flush_local_count();
		if (globalcount < delta) {
			spin_unlock(&gblcnt_mutex);
			return 0;
		}
	}
	globalcount -= delta;
	balance_count();
	spin_unlock(&gblcnt_mutex);
	return 1;
}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim_sig:read,commandchars=\\\@\$]
unsigned long read_count(void)
{
	int t;
	unsigned long sum;

	spin_lock(&gblcnt_mutex);
	sum = globalcount;
	for_each_thread(t)
		if (counterp[t] != NULL)
			sum += READ_ONCE(*counterp[t]);
	spin_unlock(&gblcnt_mutex);
	return sum;
}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim_sig:initialization,commandchars=\\\@\$]
void count_init(void)					//\lnlbl{init:b}
{
	struct sigaction sa;

	sa.sa_handler = flush_local_count_sig;
	sigemptyset(&sa.sa_mask);
	sa.sa_flags = 0;
	if (sigaction(SIGUSR1, &sa, NULL) != 0) {
		perror("sigaction");
		exit(EXIT_FAILURE);
	}
}							//\lnlbl{init:e}

void count_register_thread(void)
{
	int idx = smp_thread_id();

	spin_lock(&gblcnt_mutex);
	counterp[idx] = &counter;
	countermaxp[idx] = &countermax;
	theftp[idx] = &theft;
	spin_unlock(&gblcnt_mutex);
}

void count_unregister_thread(int nthreadsexpected)
{
	int idx = smp_thread_id();

	spin_lock(&gblcnt_mutex);
	globalize_count();
	counterp[idx] = NULL;
	countermaxp[idx] = NULL;
	theftp[idx] = NULL;
	spin_unlock(&gblcnt_mutex);
}
//\end{snippet}

void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "limtorture.h"
