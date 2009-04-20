/*
 * forkjoin.c: Demonstrate use of POSIX fork() and wait() primitives
 * 	for parallel processing.
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
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include "../api.h"

int x = 0;

int main(int argc, char *argv[])
{
	int pid;

	pid = fork();
	if (pid == 0) { /* child */
		x = 1;
		printf("Child process set x=1\n");
		exit(0);
	}
	if (pid < 0) { /* parent, upon error */
		perror("fork");
		exit(-1);
	}

	/* parent */

	waitall();
	printf("Parent process sees x=%d\n", x);

	return 0;
}
