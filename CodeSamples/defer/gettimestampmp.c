/*
 * gettimestampmp.c: Test timestamp multi-processor functionality
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

#define MAX_TIMESTAMPS 20
#define CURTIMESTAMP_MASK 0x1

long long ts[MAX_TIMESTAMPS] = {0};
long curtimestamp = 0;

void *collect_timestamps(void *mask_in)
{
	long mask = (intptr_t)mask_in;
	long cts;

	for (;;) {
		cts = READ_ONCE(curtimestamp);
		if (cts >= MAX_TIMESTAMPS)
			break;
		if ((cts & CURTIMESTAMP_MASK) != mask)
			continue;

		/* Don't need memory barrier -- no other shared vars!!! */

		ts[cts] = get_timestamp();
		WRITE_ONCE(curtimestamp, cts + 1);
	}
	smp_mb();
	return (NULL);
}

int main(int argc, char *argv[])
{
	int i;

	smp_init();

	create_thread(collect_timestamps, (void *)0);
	create_thread(collect_timestamps, (void *)1);
	wait_all_threads();
	for (i = 0; i < sizeof(ts) / sizeof(ts[0]); i++) {
		printf("%llx", ts[i]);
		if (i > 0)
			printf(" %lld", ts[i] - ts[i - 1]);
		printf("\n");
	}
	return EXIT_SUCCESS;
}
