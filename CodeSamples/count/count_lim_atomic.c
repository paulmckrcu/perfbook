/*
 * count_lim_atomic.c: simple limit counter that uses atomic operations
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

static void balance_count(void);

//\begin{snippet}[labelbase=ln:count:count_lim_atomic:var_access,commandchars=\\\@\$]
atomic_t __thread counterandmax = ATOMIC_INIT(0);	//\lnlbl{var:candmax}
unsigned long globalcountmax = 1 << 25;			//\lnlbl{var:def:b}
unsigned long globalcount = 0;
unsigned long globalreserve = 0;
atomic_t *counterp[NR_THREADS] = { NULL };
DEFINE_SPINLOCK(gblcnt_mutex);				//\lnlbl{var:def:e}
#define CM_BITS (sizeof(atomic_t) * 4)			//\lnlbl{var:CM_BITS}
#define MAX_COUNTERMAX ((1 << CM_BITS) - 1)		//\lnlbl{var:MAX_CMAX}

static __inline__ void					//\lnlbl{split_int:b}
split_counterandmax_int(int cami, int *c, int *cm)
{
	*c = (cami >> CM_BITS) & MAX_COUNTERMAX;	//\lnlbl{split_int:msh}
	*cm = cami & MAX_COUNTERMAX;			//\lnlbl{split_int:lsh}
}							//\lnlbl{split_int:e}

static __inline__ void					//\lnlbl{split:b}
split_counterandmax(atomic_t *cam, int *old, int *c, int *cm)//\lnlbl{split:func}
{
	unsigned int cami = atomic_read(cam);		//\lnlbl{split:int}

	*old = cami;					//\lnlbl{split:old}
	split_counterandmax_int(cami, c, cm);		//\lnlbl{split:split_int}
}							//\lnlbl{split:e}

static __inline__ int merge_counterandmax(int c, int cm)//\lnlbl{merge:b}
{
	unsigned int cami;

	cami = (c << CM_BITS) | cm;			//\lnlbl{merge:merge}
	return ((int)cami);
}							//\lnlbl{merge:e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim_atomic:utility1,commandchars=\\\@\$]
static void globalize_count(void)			//\lnlbl{globalize:b}
{
	int c;
	int cm;
	int old;

	split_counterandmax(&counterandmax, &old, &c, &cm);//\lnlbl{globalize:split}
	globalcount += c;
	globalreserve -= cm;
	old = merge_counterandmax(0, 0);
	atomic_set(&counterandmax, old);
}							//\lnlbl{globalize:e}

static void flush_local_count(void)			//\lnlbl{flush:b}
{
	int c;
	int cm;
	int old;
	int t;
	int zero;

	if (globalreserve == 0)				//\lnlbl{flush:checkrsv}
		return;					//\lnlbl{flush:return:n}
	zero = merge_counterandmax(0, 0);		//\lnlbl{flush:initzero}
	for_each_thread(t)				//\lnlbl{flush:loop:b}
		if (counterp[t] != NULL) {		//\lnlbl{flush:checkp}
			old = atomic_xchg(counterp[t], zero);//\lnlbl{flush:atmxchg}
			split_counterandmax_int(old, &c, &cm);//\lnlbl{flush:split}
			globalcount += c;		//\lnlbl{flush:glbcnt}
			globalreserve -= cm;		//\lnlbl{flush:glbrsv}
		}					//\lnlbl{flush:loop:e}
}							//\lnlbl{flush:e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim_atomic:add_sub,commandchars=\\\@\$]
int add_count(unsigned long delta)			//\lnlbl{add:b}
{
	int c;
	int cm;
	int old;
	int new;

	do {						//\lnlbl{add:fast:b}
		split_counterandmax(&counterandmax, &old, &c, &cm);//\lnlbl{add:split}
		if (delta > MAX_COUNTERMAX || c + delta > cm)//\lnlbl{add:check}
			goto slowpath;			//\lnlbl{add:goto}
		new = merge_counterandmax(c + delta, cm);//\lnlbl{add:merge}
	} while (atomic_cmpxchg(&counterandmax,		//\lnlbl{add:atmcmpex}
	                        old, new) != old);	//\lnlbl{add:loop:e}
	return 1;					//\lnlbl{add:return:fs}
slowpath:						//\lnlbl{add:slow:b}
	spin_lock(&gblcnt_mutex);			//\lnlbl{add:acquire}
	globalize_count();				//\lnlbl{add:globalize}
	if (globalcountmax - globalcount -		//\lnlbl{add:checkglb:b}
	    globalreserve < delta) {			//\lnlbl{add:checkglb:e}
		flush_local_count();			//\lnlbl{add:flush}
		if (globalcountmax - globalcount -	//\lnlbl{add:checkglb:nb}
		    globalreserve < delta) {		//\lnlbl{add:checkglb:ne}
			spin_unlock(&gblcnt_mutex);	//\lnlbl{add:release:f}
			return 0;			//\lnlbl{add:return:sf}
		}
	}
	globalcount += delta;				//\lnlbl{add:addglb}
	balance_count();				//\lnlbl{add:balance}
	spin_unlock(&gblcnt_mutex);			//\lnlbl{add:release:s}
	return 1;					//\lnlbl{add:return:ss}
}							//\lnlbl{add:e}

int sub_count(unsigned long delta)			//\lnlbl{sub:b}
{
	int c;
	int cm;
	int old;
	int new;

	do {						//\lnlbl{sub:fast:b}
		split_counterandmax(&counterandmax, &old, &c, &cm);
		if (delta > c)
			goto slowpath;
		new = merge_counterandmax(c - delta, cm);
	} while (atomic_cmpxchg(&counterandmax,
	                        old, new) != old);
	return 1;					//\lnlbl{sub:fast:e}
 slowpath:						//\lnlbl{sub:slow:b}
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
	return 1;					//\lnlbl{sub:slow:e}
}							//\lnlbl{sub:e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim_atomic:read,commandchars=\\\@\$]
unsigned long read_count(void)				//\lnlbl{b}
{
	int c;
	int cm;
	int old;
	int t;
	unsigned long sum;

	spin_lock(&gblcnt_mutex);			//\lnlbl{acquire}
	sum = globalcount;				//\lnlbl{initsum}
	for_each_thread(t)				//\lnlbl{loop:b}
		if (counterp[t] != NULL) {
			split_counterandmax(counterp[t], &old, &c, &cm);//\lnlbl{split}
			sum += c;
		}					//\lnlbl{loop:e}
	spin_unlock(&gblcnt_mutex);			//\lnlbl{release}
	return sum;					//\lnlbl{return}
}							//\lnlbl{e}
//\end{snippet}

void count_init(void)
{
}

//\begin{snippet}[labelbase=ln:count:count_lim_atomic:utility2,commandchars=\\\@\$]
static void balance_count(void)				//\lnlbl{balance:b}
{
	int c;
	int cm;
	int old;
	unsigned long limit;

	limit = globalcountmax - globalcount -
	        globalreserve;
	limit /= num_online_threads();
	if (limit > MAX_COUNTERMAX)
		cm = MAX_COUNTERMAX;
	else
		cm = limit;
	globalreserve += cm;
	c = cm / 2;
	if (c > globalcount)
		c = globalcount;
	globalcount -= c;
	old = merge_counterandmax(c, cm);
	atomic_set(&counterandmax, old);		//\lnlbl{balance:atmcset}
}							//\lnlbl{balance:e}

void count_register_thread(void)			//\lnlbl{register:b}
{
	int idx = smp_thread_id();

	spin_lock(&gblcnt_mutex);
	counterp[idx] = &counterandmax;
	spin_unlock(&gblcnt_mutex);
}

void count_unregister_thread(int nthreadsexpected)	//\lnlbl{unregister:b}
{
	int idx = smp_thread_id();

	spin_lock(&gblcnt_mutex);
	globalize_count();
	counterp[idx] = NULL;
	spin_unlock(&gblcnt_mutex);
}
//\end{snippet}

void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "limtorture.h"
