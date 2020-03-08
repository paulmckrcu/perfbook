#!/bin/bash
#
# Reduce data gathered by cachetorture.sh.  Run in the directory where
# you want the files deposited.  Or you can place an absolute pathname
# in the tag, I suppose.
#
# Usage: bash reduce.sh [ tag [ cpu ] ] < cachetorture.sh.out
#
#	If present, the "tag" will be included in the output filenames,
#	for example, <tag>.atomicinc.dat.  The output files are
#	formatted for use as gnuplot data files.  One format for <tag>
#	is <system-id>.yyyy.mm.ddA.  If "cpu" is given, only the data
#	with that CPU as cpu0 will be considered.
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
# Copyright (C) Facebook, 2020
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

tag="$1"
firstcpu="${2-0}"

# Gather data from each operation into a separate .raw file.
# Each line has the program name, the operation name, the pair of CPUs
# used, the duration, and finally the nanoseconds per operation.
awk -v tag="$tag" -v firstcpu="$firstcpu" '
{
	opname = $2;
	cpu0 = $4;
	if (cpu0 != firstcpu)
		next;
	cpu1 = $5;
	nsperop = $9;
	i = opname ":" cpu0 ":" cpu1
	# print "Read this: " opname, cpu0, cpu1, nsperop, "idx: " i
	fn = tag "." opname ".sctr.raw"
	print(cpu0, cpu1, nsperop) > fn
	sum[i] += nsperop;
	n[i]++;
	if (min[i] == "" || min[i] > nsperop)
		min[i] = nsperop;
	if (max[i] == "" || max[i] < nsperop)
		max[i] = nsperop;
}

END	{
	for (i in n) {
		split(i, idx, ":");
		opname = idx[1];
		cpu0 = idx[2];
		cpu1 = idx[3];
		fn = tag "." opname ".raw"
		# print fn ": " cpu0, cpu1, sum[i] / n[i], min[i], max[i]
		print(cpu0, cpu1, sum[i] / n[i], min[i], max[i]) > fn
	}
}'

# Extract the read-side data into a .dat file formatted for gnuplot
# (average then minimum then maximum).
for i in `ls $tag.*.raw`
do
	bn=`echo $i | sed -e 's/\.raw//'`
	sort -k2n < $i |
	awk > $bn.dat '{ print $2, $3}'
done
