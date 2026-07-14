/*-
 * Copyright (c) 1992, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	from: @(#)random.c	8.1 (Berkeley) 6/10/93
 *      $Id: random.c,v 1.10 2004/09/13 02:04:28 paulmck Exp paulmck $
 */

/*
 * Modified 4/10/2003 to allow parallel operation.
 * Modified 5/18/2014 to use __thread.
 * Copyright (c) 2014-2019 IBM Corporation.
 * Copyright (c) 2019 Facebook.
 */

#include <sys/types.h>
#include <stdio.h>
#include <stdlib.h>

/*
 * Park-Miller state for this thread.  The valid states are [1, 2^31 - 2]:
 * zero is the recurrence's absorbing state, and 2^31 - 1 is a fixed point.
 * Leave this zero-initialized, so that a thread that never seeds itself is
 * caught by myrandom() below rather than silently drawing the same sequence
 * as every other unseeded thread.
 */
static u_long __thread randseed;

/*
 * Set the seed for the current thread.  Seeds congruent to zero
 * modulo 2^31 - 1 (that is, 0, 0x7fffffff, and 0xfffffffe) would
 * put the Park-Miller recurrence into its absorbing state, so map
 * them to 1.
 */
void
setrandom(unsigned int seed)
{
	randseed = seed % 0x7fffffff;
	if (randseed == 0)
		randseed = 1;
}

/*
 * Seed the current thread from a thread ID, so that each thread draws its
 * own sequence.  randseed is __thread: seeding one thread does not seed the
 * others, so every thread that draws must call this (or setrandom()) itself.
 *
 * Scale the ID by a large odd constant rather than using it directly.  All
 * seeds lie on the same Park-Miller cycle, so seeding only chooses a starting
 * offset, and adjacent offsets are not as independent as they look: 16807 *
 * even is even, and callers such as random_level() in skiplist.h count
 * trailing 1-bits, so consecutive IDs would hand every even-numbered thread
 * the same parity on its first draw.
 *
 * The seed depends only on the ID, so a run remains reproducible.
 */
void
setrandom_thread(unsigned int id)
{
	setrandom(2654435761U * (id + 1));
}

/*
 * Pseudo-random number generator for randomizing the profiling clock,
 * and whatever else we might use it for.  The result is uniform on
 * [1, 2^31 - 2].
 */
u_long
myrandom(void)
{
	register long x, hi, lo, t;

	/*
	 * Catch an unseeded thread (randseed == 0, the absorbing state),
	 * 2^31 - 1 (a fixed point), and anything else outside the
	 * recurrence's state space.  Each of these degrades the generator
	 * silently rather than failing: an unseeded thread draws in lockstep
	 * with every other unseeded thread, and a fixed point returns the
	 * same value forever.
	 */
	if (randseed == 0 || randseed > 0x7ffffffe) {
		fprintf(stderr,
			"myrandom(): randseed %#lx is outside [1, 2^31 - 2].\n"
			"Each thread must seed itself, for example with "
			"setrandom_thread(): randseed is __thread, so seeding "
			"one thread does not seed the others.\n", randseed);
		abort();
	}

	/*
	 * Compute x[n + 1] = (7^5 * x[n]) mod (2^31 - 1).
	 * From "Random number generators: good ones are hard to find",
	 * Park and Miller, Communications of the ACM, vol. 31, no. 10,
	 * October 1988, p. 1195.
	 */
	x = randseed;
	hi = x / 127773;
	lo = x % 127773;
	t = 16807 * lo - 2836 * hi;
	if (t <= 0)
		t += 0x7fffffff;
	randseed = t;
	return (t);
}

#ifdef TEST

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
	int i;
	u_long seed = 0;

	if (argc > 1)
		seed = strtoul(argv[1], NULL, 0);
	printf("seed = %#lx\n", seed);
	setrandom(seed);
	for (i = 0; i < 20; i++)
		printf("%d: %#lx\n", i, myrandom());
}

#endif
