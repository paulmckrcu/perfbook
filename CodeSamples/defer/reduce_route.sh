#!/bin/bash
#
# Reduce data gathered by route_perf.sh.
#
# Usage: bash route_reduce.sh [ tag ] < route_perf.sh.out
#
#	If present, the "tag" will be included in the output filenames,
#	for example, count_nonatomic:r.<tag>.dat.  The output files are
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
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright (C) IBM Corporation, 2016-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

tag="$1"

# Gather data from each program into a separate .raw file.
# Each line has the number of CPUs followed by read data points followed
# by write data points.
grep -v '^ns/read:' |
awk -v tag="$tag" '
BEGIN	{
	progname = "";
}

/^route_/ {
	progname = $1;
	ncpus = $4;
	next;
}

$1 == "nlookups:" && progname != "" {
	if ($2 != "nan") {
		datasets["" progname] = 1;
		key = "" progname ":" ncpus;
		data[key] = data[key] " " $2 / $10;
		if (mincpu == "" || mincpu > ncpus)
			mincpu = ncpus;
		if (maxcpu == "" || maxcpu < ncpus)
			maxcpu = ncpus;
	}
}

{
	progname = "";
}

END	{
	for (i in datasets) {
		progname = i;
		for (ncpus = mincpu; ncpus <= maxcpu; ncpus++) {
			key = i ":" ncpus;
			if (data[key] != "") {
				print(ncpus, data[key]) > "" i "." tag ".raw"
			}
		}
	}
}'

# Extract the read-side data into a .dat file formatted for gnuplot
# (average then minimum then maximum).
for i in `ls *$tag.raw`
do
	bn=`echo $i | sed -e 's/\.raw//'`
	awk < $i > $bn.dat '
		{
			cpus = $1;
			min = $2;
			max = $2;
			sum = 0;
			n = 0;
			for (i = 2; i <= (NF - 1) / 2 + 1; i++) {
				sum += $i;
				n++;
				if ($i < min)
					min = $i;
				if ($i > max)
					max = $i;
			}
			print cpus, sum / n, min, max;
		}'
done
