/*
 * Double-precision gettimeofday() in seconds.
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
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

/*
 * Return time of day, in decimal seconds since 1970.
 */
double dgettimeofday(void)
{
	struct timeval tv;

	if (gettimeofday(&tv, NULL) != 0) {
		perror("gettimeofday");
		exit(-1);
	}

	return (tv.tv_sec + ((double)tv.tv_usec) / 1000000.);
}

#ifdef TEST

int main(int argc, char *argv[])
{
	printf("time = %.6f\n", dgettimeofday());
	exit(0);
}

#endif /* #ifdef TEST */
