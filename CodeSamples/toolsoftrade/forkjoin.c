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
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/wait.h>
#include "../api.h"

int main(int argc, char *argv[])
{
	int i;
	int nforks;
	int pid;
	int stat_val;

	if (argc != 2) {
		fprintf(stderr, "Usage: %s nforks\n", argv[0]);
		exit(EXIT_FAILURE);
	}
	nforks = atoi(argv[1]);
	printf("%d fork()s\n", nforks);
	printf("Starting at ");
	fflush(stdout);
	stat_val = system("date");
	if (!WIFEXITED(stat_val) || WEXITSTATUS(stat_val)) {
		fprintf(stderr, "system(\"date\") failed: %x\n", stat_val);
	}
	for (i = 0; i < nforks; i++) {
		pid = fork();
		if (pid == 0) { /* child */
			sleep(3);
			exit(0);
		}
		if (pid < 0) { /* parent, upon error */
			perror("fork");
			exit(EXIT_FAILURE);
		}
	}

	/* parent */

	waitall();
	printf("Finished at ");
	fflush(stdout);
	stat_val = system("date");
	if (!WIFEXITED(stat_val) || WEXITSTATUS(stat_val)) {
		fprintf(stderr, "system(\"date\") failed: %x\n", stat_val);
	}

	return EXIT_SUCCESS;
}
