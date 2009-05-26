/*
 * forkjoinperf.c: Measure fork()/join() overhead.
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

int main(int argc, char *argv[])
{
	int i;
	int nforks;
	int pid;
	int status;

	if (argc != 2) {
		fprintf(stderr, "Usage: %s nforks\n", argv[0]);
		exit(-1);
	}
	nforks = atoi(argv[1]);
	printf("%d fork()s\n", nforks);
	printf("Starting at ");
	fflush(stdout);
	system("date");
	for (i = 0; i < nforks; i++) {
		pid = fork();
		if (pid == 0) { /* child */
			exit(0);
		}
		if (pid < 0) { /* parent, upon error */
			perror("fork");
			exit(-1);
		}
		for (;;) {
			pid = wait(&status);
			if (pid == -1) {
				if (errno == ECHILD)
					break;
				perror("wait");
				exit(-1);
			}
		}
	}
	printf("Finished at ");
	fflush(stdout);
	system("date");

	return 0;
}
