/*
 * gettimestamp.c: Test timestamp functionality
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
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
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
	exit(0);
}
