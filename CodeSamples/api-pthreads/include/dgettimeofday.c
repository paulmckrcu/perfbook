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
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
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

/*
 * Spin waiting for the specified number of microseconds.
 */
void wait_microseconds(double usecs)
{
	double starttime;
	double stoptime;

	if (usecs == 0)
		return;
	starttime = dgettimeofday();
	stoptime = starttime + usecs / 1000000.;
	do {
	} while (dgettimeofday() < stoptime);
}

#ifdef TEST

int main(int argc, char *argv[])
{
	printf("time = %.6f\n", dgettimeofday());
	exit(0);
}

#endif /* #ifdef TEST */
