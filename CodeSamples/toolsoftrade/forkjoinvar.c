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
#include "../api.h"

// \begin{snippet}[labelbase=ln:toolsoftrade:forkjoinvar:main,keepcomment=yes,commandchars=\$\@\^]
int x = 0;

int main(int argc, char *argv[])
{
	int pid;

	pid = fork();
	if (pid == 0) { /* child */
		x = 1;					//\lnlbl{setx}
		printf("Child process set x=1\n");	//\lnlbl{print:c}
		exit(EXIT_SUCCESS);			//\lnlbl{exit:s}
	}
	if (pid < 0) { /* parent, upon error */
		perror("fork");
		exit(EXIT_FAILURE);
	}

	/* parent */

	waitall();					//\lnlbl{waitall}
	printf("Parent process sees x=%d\n", x);	//\lnlbl{print:p}

	return EXIT_SUCCESS;
}
// \end{snippet}
