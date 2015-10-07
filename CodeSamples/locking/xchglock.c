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
 * Copyright (c) 2011 Paul E. McKenney, IBM Corporation.
 */

#include "../api.h"

typedef int xchglock_t;

#define DEFINE_XCHG_LOCK(n) xchglock_t n = 0

void xchg_lock(xchglock_t *xp)
{
	while (xchg(xp, 1) == 1) {
		while (*xp == 1)
			continue;
	}
}

void xchg_unlock(xchglock_t *xp)
{
	(void)xchg(xp, 0);
}

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
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 1);
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
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
	goflag = GOFLAG_RUN;
	smp_mb();
	poll(NULL, 0, 10000);
	smp_mb();
	goflag = GOFLAG_STOP;
	smp_mb();
	wait_all_threads();
	printf("lockacqs = %lu, lockerr = %lu\n", lockacqs, lockerr);
	return 0;
}
