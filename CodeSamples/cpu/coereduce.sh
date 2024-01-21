#!/bin/bash
#
# Reduce temporal coe data that has been previously collected, for
# example, using: "./temporal --coe --nthreads 15".  Note that the
# output of coe.sh is -not- suitable.
#
# Usage: bash coereduce.sh
#
# Takes the temporal coe data as standard input and produces on standard
# output a gnuplot .dat file that plots the number of distinct opinions
# on the value of the shared variable as a function of time.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright (C) Meta Platform Inc., 2023
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

awk '
/^[0-9][0-9]* / {
	print $3, $2, +1;
	print $3, $6, -1;
}' | sort -k2n |
awk '
BEGIN {
	max = -1;
	xmin="";
}

{
	if (xmin == "")
		xmin = $2 - 25;
	if ($3 > 0) {
		if (nv[$1]++ == 0) {
			n = n + 1;
			print $2 - xmin, n - 1;
			print $2 - xmin, n;
			if (n > max)
				max = n;
		}
	} else {
		if (--nv[$1] == 0) {
			n = n - 1;
			print $2 - xmin, n + 1;
			print $2 - xmin, n;
		}
	}
}

END {
	if (n != 0) {
		print "# Ending value of n = ", n "!!!";
		exit 1;
	}
	print "# Maximum number of values: " max;
}'
