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

#\begin{snippet}[labelbase=ln:debugging:datablows:whole,commandchars=\!\@\%]
div=3				#\lnlbl{param:b}
rel=0.01
tre=10				#\lnlbl{param:e}
while test $# -gt 0		#\lnlbl{parse:b}
do
	case "$1" in
	--divisor)
		shift
		div=$1
		;;
	--relerr)
		shift
		rel=$1
		;;
	--trendbreak)
		shift
		tre=$1
		;;
	esac
	shift
done				#\lnlbl{parse:e}
# echo divisor: $div relerr: $rel trendbreak: $tre #\fcvexclude

awk -v divisor=$div -v relerr=$rel -v trendbreak=$tre '{#\lnlbl{awk:invoke}
	for (i = 2; i <= NF; i++)		#\lnlbl{awk:copy:b}
		d[i - 1] = $i;			#\lnlbl{awk:copy:e}
	asort(d);				#\lnlbl{awk:asort}
	i = int((NF + divisor - 1) / divisor);	#\lnlbl{awk:comp_i}
	delta = d[i] - d[1];			#\lnlbl{awk:delta}
	maxdelta = delta * divisor;		#\lnlbl{awk:maxdelta}
	maxdelta1 = delta + d[i] * relerr;	#\lnlbl{awk:maxdelta1}
	if (maxdelta1 > maxdelta)		#\lnlbl{awk:comp_max:b}
		maxdelta = maxdelta1;		#\lnlbl{awk:comp_max:e}
	for (j = i + 1; j < NF; j++) {		#\lnlbl{awk:add:b}
		if (j <= 2)			#\lnlbl{awk:chk_engh}
			maxdiff = d[NF - 1] - d[1];
		else
			maxdiff = trendbreak * (d[j - 1] - d[1]) / (j - 2); #\lnlbl{awk:mul_avr}
# print "i: " i, "j: " j, "maxdelta: " maxdelta, "maxdiff: " maxdiff, "d[j] - d[j - 1]: " d[j] - d[j - 1] #\fcvexclude
		if (d[j] - d[1] > maxdelta && d[j] - d[j - 1] > maxdiff) #\lnlbl{awk:chk_max}
			break;			#\lnlbl{awk:break}
	}					#\lnlbl{awk:add:e}
	n = sum = 0;				#\lnlbl{awk:comp_stat:b}
	for (k = 1; k < j; k++) {
		sum += d[k];
		n++;
	}
	min = d[1];
	max = d[j - 1];
	avg = sum / n;
	print $1, avg, min, max, n, NF - 1;	#\lnlbl{awk:comp_stat:e}
}'						#\lnlbl{awk:end}
#\end{snippet}
