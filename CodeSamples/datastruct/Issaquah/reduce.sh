#!/bin/sh
#
# reduce: Convert ./treetorture stresstest output to .dat file
#
#	Grep out lines beginning with "--" before feeding to gnuplot.
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
# Copyright (c) 2014-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

awk '
/^\.\/treetorture/ {
	havesome = 0;
	nupdaters = 1;
	for (i = 1; i <= NF; i++)
		if ($i == "--nupdaters") {
			nupdaters = $(i + 1);
		}
	print "--nupdaters = " nupdaters;
}

/^Duration:/ {
	duration = $2 / 1000;
	print "--duration = " duration;
}

/^lookups:/ {
	lookups = $2;
	scans = $5;
	ins = $7;
	dels = $11;
	moves = $16;
	print "--lookups = " lookups "  scans = " scans "  ins = " ins "  dels = " dels "  moves = " moves;
	sum = lookups + scans + ins + dels + moves;
	print "--lookupfrac = " lookups / sum;
	print "--ops per CPU per millisecond: " sum / nupdaters / duration;
	ratio = sum / duration;
	print "--subtotal: " nupdaters, ratio;
	totsum[nupdaters] += sum;
	totduration[nupdaters] += duration;
	if (minratio[nupdaters] == "" || ratio < minratio[nupdaters])
		minratio[nupdaters] = ratio;
	if (maxratio[nupdaters] == "" || ratio > maxratio[nupdaters])
		maxratio[nupdaters] = ratio;
}

END {
	for (i in totsum) {
		print i, totsum[i] / totduration[i], minratio[i], maxratio[i];
	}
}'
