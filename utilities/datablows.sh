#!/bin/sh
#
# Input a file where each line has an x-value followed by a series of
# y-values in sorted order.  Output a line containing the x-value, the
# average, min, and max of the good data, the number of good data values,
# and the number of original data values.  This script uses a variant of
# the old Sonatech data-cleaning algorithm, but incorporates the assumption
# that the smallest data values are good.  Similar algorithms have been
# used by Dave Mills in NTP and by Larry McVoy in lmbench.
#
# This script takes the following arguments:
#
#	--divisor:  Reciprocal of the leading fraction of data assumed
#		to be good, defaults to 3 (for one-third of the data).
#	--relerr:  Relative error inherent in the data, defaults to 0.01.
#	--trendbreak:  Multiple of average difference deemed to constitute
#		a trend break.  Defaults to 2.
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
# Copyright (C) IBM Corporation, 2012
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

divisor=3
relerr=0.01
trendbreak=10
while test $# -gt 0
do
	case "$1" in
	--divisor)
		shift
		divisor=$1
		;;
	--relerr)
		shift
		relerr=$1
		;;
	--trendbreak)
		shift
		trendbreak=$1
		;;
	esac
	shift
done
# echo divisor: $divisor relerr: $relerr trendbreak: $trendbreak

awk -v divisor=$divisor -v relerr=$relerr -v trendbreak=$trendbreak '{
	for (i = 2; i <= NF; i++)
		d[i - 1] = $i;
	asort(d);
	i = int((NF + divisor - 1) / divisor);
	delta = d[i] - d[1];
	maxdelta = delta * divisor;
	maxdelta1 = delta + d[i] * relerr;
	if (maxdelta1 > maxdelta)
		maxdelta = maxdelta1;
	for (j = i + 1; j < NF; j++) {
		if (j <= 2)
			maxdiff = d[NF - 1] - d[1];
		else
			maxdiff = trendbreak * (d[j - 1] - d[1]) / (j - 2);
# print "i: " i, "j: " j, "maxdelta: " maxdelta, "maxdiff: " maxdiff, "d[j] - d[j - 1]: " d[j] - d[j - 1]
		if (d[j] - d[1] > maxdelta && d[j] - d[j - 1] > maxdiff)
			break;
	}
	n = sum = 0;
	for (k = 1; k < j; k++) {
		sum += d[k];
		n++;
	}
	min = d[1];
	max = d[j - 1];
	avg = sum / n;
	print $1, avg, min, max, n, NF - 1;
}'
