#!/bin/bash
#
# Plot the data reduced by reduce.sh.  Run in the directory where
# reduce.sh deposited the data.
#
# Usage: bash plots.sh
#
# This script plots only the CAS and local data, though it preps all
# of the data that reduce.sh currently produces.
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
# Copyright (C) Meta Platforms Inc., 2023
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

T="`mktemp -d ${TMPDIR-/tmp}/plots.sh.XXXXXX`"
trap 'rm -rf $T' 0 2

tag="`ls *.atomicinc.sctr.dat | sed -e 's/.atomicinc.sctr.dat$//'`"

# Copy over the multi-valued scatter data
cp "${tag}.atomicinc.sctr.dat" $T/"Atomic increment"
awk < "${tag}.blindcmpxchg.sctr.dat" > $T/"Blind cmpxchg" '{ print $1 + 0.25, $2; }'
awk < "${tag}.cmpxchg.sctr.dat" > $T/"cmpxchg" '{ print $1 + 0.5, $2; }'
awk < "${tag}.write.sctr.dat" > $T/"Write" '{ print $1 + 0.75, $2; }'

# Just average values for the local data
lastcpu="`tail -1 ${tag}.atomicinc.dat | awk '{print $1; }'`"
for i in localcmpxchg locallock
do
	label="`echo ${i} | sed -e 's/^local/Local /'`"
	value="`tail -1 ${tag}.${i}.dat | awk '{print $2; }'`"
	awk -v "lastcpu=${lastcpu}" -v "value=${value}" < /dev/null '
	BEGIN {
		for (i = 0; i <= lastcpu; i++)
			print i, value;
	}' > "$T/${label}"
done

awk -v "lastcpu=${lastcpu}" '
BEGIN {
	if (lastcpu >= 128) {
		print "w dots";
	} else {
		print "w points pt 6 ps 1"
	}
}' > $T/withstring
ws="`cat $T/withstring`"

resdir="`pwd`"
pushd $T > /dev/null

gnuplot << ---EOF---
set term png size 2000,800
set output "${resdir}/latencies.png"
set key tmargin
set xlabel "CPU Number (${tag})"
set ylabel "Latency (ns)"
plot "Atomic increment" ${ws}, "Blind cmpxchg" ${ws}, "cmpxchg" ${ws}, "Write" ${ws}, "Local cmpxchg" w l, "Local lock" w l
---EOF---

display "${resdir}/latencies.png"
