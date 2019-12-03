#!/bin/sh
#
# Takes the output of writecacheflow and produces a latex table showing
# the order of memory visibility.
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
# Copyright (C) IBM Corporation, 2007-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@us.ibm.com>

T=/tmp/writeflowtab.sh.$$
trap 'rm -rf $T' 0
sort --key=3n > $T

MAXCPU=`awk 'BEGIN { m = 0 } { if ($1 > m) m = $1 } END { print m }' < $T`
MINCPU=`awk 'BEGIN { m = '$MAXCPU' } { if ($1 < m) m = $1 } END { print m }' < $T`

cat $T | sed -e 's/://g' | awk '
BEGIN	{
		maxcpu = '$MAXCPU';
		mincpu = '$MINCPU';

		heading = "\\begin{tabular}{r|"
		for (i = mincpu; i <= maxcpu; i++) {
			heading = heading "|r";
		}
		print heading "}";

		heading = "    & \\multicolumn{" maxcpu - mincpu + 1 "}";
		heading = heading "{c}{Values Observed by CPUs} \\\\";
		print heading


		print "    \\cline{2-" maxcpu - mincpu + 2 "}";

		heading = "Time ";
		for (i = mincpu; i <= maxcpu; i++) {
			heading = heading "& " i " ";
		}
		print heading "\\\\";
		print "\\hline";
	}

	{
		cpu[$1] = $2;
		curtime = $3;
		endtime[$1] = $5;
		if (maxcpu < $1) {
			maxcpu = $1;
		}
		node = "";
		for (i = 1; i <= maxcpu; i++) {
			if (i == $1) {
				node = node " & \\emph(" cpu[i] ")";
			} else {
				if (endtime[i] != "" && curtime >= endtime[i]) {
					cpu[i] = "~";
				}
				node = node " & " cpu[i];
			}
		}
		print "\\hline";
		print curtime " " node " \\\\";
	}

END	{
		print "\\end{tabular}"
	}'
