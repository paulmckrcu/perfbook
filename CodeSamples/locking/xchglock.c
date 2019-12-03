/*
 * xchglock.c: Sample atomic-xchg-based lock primitive.
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
 * Copyright (c) 2011-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

//\begin{snippet}[labelbase=ln:locking:xchglock:lock_unlock,commandchars=\\\[\]]
typedef int xchglock_t;				//\lnlbl{typedef}
						//\fcvexclude
#define DEFINE_XCHG_LOCK(n) xchglock_t n = 0	//\lnlbl{initval}

void xchg_lock(xchglock_t *xp)			//\lnlbl{lock:b}
{
	while (xchg(xp, 1) == 1) {		//\lnlbl{lock:atmxchg}
		while (READ_ONCE(*xp) == 1)	//\lnlbl{lock:inner:b}
			continue;		//\lnlbl{lock:inner:e}
	}
}						//\lnlbl{lock:e}

void xchg_unlock(xchglock_t *xp)		//\lnlbl{unlock:b}
{
	(void)xchg(xp, 0);			//\lnlbl{unlock:atmxchg}
}						//\lnlbl{unlock:e}
//\end{snippet}

DEFINE_XCHG_LOCK(testlock);

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

atomic_t nthreadsrunning;

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

int owner = -1;
unsigned long lockacqs;
unsigned long lockerr;

void *test_xchg_lock(void *arg)
{
	int me = (long)arg;

	run_on(me);
	atomic_inc(&nthreadsrunning);
	while (READ_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (READ_ONCE(goflag) == GOFLAG_RUN) {
		xchg_lock(&testlock);
		if (owner != -1)
			lockerr++;
		lockacqs++;
		owner = me;
		poll(NULL, 0, 1);
		owner = -1;
		xchg_unlock(&testlock);
	}
	return NULL;
}

int main(int argc, char *argv[])
{
	int nthreads = 0;

	create_thread(test_xchg_lock, (void *)0);
	nthreads++;
	create_thread(test_xchg_lock, (void *)1);
	nthreads++;

	smp_mb();
	while (atomic_read(&nthreadsrunning) < nthreads)
		poll(NULL, 0, 1);
	WRITE_ONCE(goflag, GOFLAG_RUN);
	smp_mb();
	poll(NULL, 0, 10000);
	smp_mb();
	WRITE_ONCE(goflag, GOFLAG_STOP);
	smp_mb();
	wait_all_threads();
	printf("lockacqs = %lu, lockerr = %lu\n", lockacqs, lockerr);
	return 0;
}
