/*
 * gettimestamp.c: Test timestamp functionality
 *
 * Usage: ./gettimestamp
 *
 * Output:
 *
 * 3c270dbdd2ec
 * 3c270dbdd3c9 221
 * 3c270dbdd4a6 221
 * 3c270dbdd576 208
 * 3c270dbdd653 221
 * 3c270dbdd730 221
 * 3c270dbdd80d 221
 * 3c270dbdd8ea 221
 * 3c270dbdd9c7 221
 * 3c270dbddaa4 221
 *
 * The first number on each line is the hexadecimal number returned
 * by the fine-grained timer (rdtsc on x86, TBR on Power).  The second
 * number is the decimal difference between the line in question and
 * its predecessor.
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
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"
#include "rcu.h"

int main(int argc, char *argv[])
{
	int i;
	long long ts[10];

	smp_init();

	for (i = 0; i < sizeof(ts) / sizeof(ts[0]); i++)
		ts[i] = get_timestamp();
	for (i = 0; i < sizeof(ts) / sizeof(ts[0]); i++) {
		printf("%llx", ts[i]);
		if (i > 0)
			printf(" %lld", ts[i] - ts[i - 1]);
		printf("\n");
	}
	return EXIT_SUCCESS;
}
