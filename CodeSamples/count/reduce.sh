#!/bin/bash
#
# Reduce data gathered by perf.sh.
#
# Usage: bash reduce.sh [ tag ] < perf.sh.out
#
#	If present, the "tag" will be included in the output filenames,
#	for example, count_nonatomic.r.<tag>.dat.  The output files are
#	formatted for use as gnuplot data files.
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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
#
# Copyright (C) IBM Corporation, 2008
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

tag="$1"

grep -v '^!!!' | grep -v "^n_reads:" |
awk '
BEGIN	{
	tag = "'"$tag"'";
	progname = "";
}

	{
	if ($1 != "ns/read:") {
		progname = $1;
		ncpus = $2;
	} else if ($1 == "ns/read:" && progname != "") {
		if ($2 != "nan") {
			datasets["" progname ":r"] = 1;
			key = "" progname ":r:" ncpus;
			data[key] = data[key] " " $2;
		}
		if ($4 != "nan") {
			datasets["" progname ":u"] = 1;
			key = "" progname ":u:" ncpus;
			data[key] = data[key] " " $4;
		}
		if ($2 != "nan" || $4 != "nan") {
			if (mincpu == "" || mincpu > ncpus)
				mincpu = ncpus;
			if (maxcpu == "" || maxcpu < ncpus)
				maxcpu = ncpus;
		}
		progname = "";
	} else {
		progname = "";
	}
}

END	{
	for (i in datasets) {
		split(i, a, ":");
		progname = a[1];
		uflag = a[2];
		for (ncpus = mincpu; ncpus <= maxcpu; ncpus++) {
			key = i ":" ncpus;
			if (data[key] != "") {
				print(ncpus, data[key]) > "" i "." tag ".raw"
			}
		}
	}
}'
