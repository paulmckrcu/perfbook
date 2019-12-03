/*
 * count_lim.c: simple limit counter.
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

static __inline__ void globalize_count(void);
static __inline__ void balance_count(void);

//\begin{snippet}[labelbase=ln:count:count_lim:variable,commandchars=\\\@\$]
unsigned long __thread counter = 0;
unsigned long __thread countermax = 0;
unsigned long globalcountmax = 10000;		//\lnlbl{globalcountmax}
unsigned long globalcount = 0;			//\lnlbl{globalcount}
unsigned long globalreserve = 0;		//\lnlbl{globalreserve}
unsigned long *counterp[NR_THREADS] = { NULL };
DEFINE_SPINLOCK(gblcnt_mutex);
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim:add_sub_read,commandchars=\\\@\$]
static __inline__ int add_count(unsigned long delta)	//\lnlbl{add:b}
{
	if (countermax - counter >= delta) {		//\lnlbl{add:checklocal}
		WRITE_ONCE(counter, counter + delta);	//\lnlbl{add:add}
		return 1;				//\lnlbl{add:return:ls}
	}
	spin_lock(&gblcnt_mutex);			//\lnlbl{add:acquire}
	globalize_count();				//\lnlbl{add:globalize}
	if (globalcountmax -				//\lnlbl{add:checkglb:b}
	    globalcount - globalreserve < delta) {	//\lnlbl{add:checkglb:e}
		spin_unlock(&gblcnt_mutex);		//\lnlbl{add:release:f}
		return 0;				//\lnlbl{add:return:gf}
	}
	globalcount += delta;				//\lnlbl{add:addglb}
	balance_count();				//\lnlbl{add:balance}
	spin_unlock(&gblcnt_mutex);			//\lnlbl{add:release:s}
	return 1;					//\lnlbl{add:return:gs}
}							//\lnlbl{add:e}

static __inline__ int sub_count(unsigned long delta)	//\lnlbl{sub:b}
{
	if (counter >= delta) {				//\lnlbl{sub:checklocal}
		WRITE_ONCE(counter, counter - delta);	//\lnlbl{sub:sub}
		return 1;				//\lnlbl{sub:return:ls}
	}
	spin_lock(&gblcnt_mutex);			//\lnlbl{sub:acquire}
	globalize_count();				//\lnlbl{sub:globalize}
	if (globalcount < delta) {			//\lnlbl{sub:checkglb}
		spin_unlock(&gblcnt_mutex);		//\lnlbl{sub:release:f}
		return 0;				//\lnlbl{sub:return:gf}
	}
	globalcount -= delta;				//\lnlbl{sub:subglb}
	balance_count();				//\lnlbl{sub:balance}
	spin_unlock(&gblcnt_mutex);			//\lnlbl{sub:release:s}
	return 1;					//\lnlbl{sub:return:gs}
}							//\lnlbl{sub:e}

static __inline__ unsigned long read_count(void)	//\lnlbl{read:b}
{
	int t;
	unsigned long sum;

	spin_lock(&gblcnt_mutex);			//\lnlbl{read:acquire}
	sum = globalcount;				//\lnlbl{read:initsum}
	for_each_thread(t)				//\lnlbl{read:loop:b}
		if (counterp[t] != NULL)
			sum += READ_ONCE(*counterp[t]);	//\lnlbl{read:loop:e}
	spin_unlock(&gblcnt_mutex);			//\lnlbl{read:release}
	return sum;					//\lnlbl{read:return}
}							//\lnlbl{read:e}
//\end{snippet}

//\begin{snippet}[labelbase=ln:count:count_lim:utility,commandchars=\\\@\$]
static __inline__ void globalize_count(void)	//\lnlbl{globalize:b}
{
	globalcount += counter;			//\lnlbl{globalize:add}
	counter = 0;				//\lnlbl{globalize:zero}
	globalreserve -= countermax;		//\lnlbl{globalize:sub}
	countermax = 0;			//\lnlbl{globalize:zeromax}
}						//\lnlbl{globalize:e}

static __inline__ void balance_count(void)	//\lnlbl{balance:b}
{
	countermax = globalcountmax -		//\lnlbl{balance:share:b}
	             globalcount - globalreserve;
	countermax /= num_online_threads();	//\lnlbl{balance:share:e}
	globalreserve += countermax;		//\lnlbl{balance:adjreserve}
	counter = countermax / 2;		//\lnlbl{balance:middle}
	if (counter > globalcount)		//\lnlbl{balance:check}
		counter = globalcount;		//\lnlbl{balance:adjcounter}
	globalcount -= counter;			//\lnlbl{balance:adjglobal}
}						//\lnlbl{balance:e}

#ifndef FCV_SNIPPET
void count_init(void)
{
}
#endif /* FCV_SNIPPET */
					//\fcvexclude
void count_register_thread(void)	//\lnlbl{register:b}
{
	int idx = smp_thread_id();

	spin_lock(&gblcnt_mutex);
	counterp[idx] = &counter;
	spin_unlock(&gblcnt_mutex);
}					//\lnlbl{register:e}

void count_unregister_thread(int nthreadsexpected)	//\lnlbl{unregister:b}
{
	int idx = smp_thread_id();

	spin_lock(&gblcnt_mutex);		//\lnlbl{unregister:acquire}
	globalize_count();			//\lnlbl{unregister:globalize}
	counterp[idx] = NULL;			//\lnlbl{unregister:clear}
	spin_unlock(&gblcnt_mutex);		//\lnlbl{unregister:release}
}						//\lnlbl{unregister:e}
//\end{snippet}

void count_cleanup(void)
{
}

#define NEED_REGISTER_THREAD
#include "limtorture.h"
