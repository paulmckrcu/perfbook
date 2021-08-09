#!/bin/sh
#
# smpalloc.sh: simple script to generate data from smpalloc.
#	Note: no attempt is made to generate statistically
#	defensible data!
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
# Copyright (c) 2006-2019 Paul E. McKenney, IBM.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

maxt=2

for ((nt = 1; nt <= $maxt; nt++))
do
	rm smpalloc.$nt.dat
	touch smpalloc.$nt.dat
	for ((nb = 1; nb < 25; nb++))
	do
		./smpalloc $nt $nb >> smpalloc.$nt.dat
		sleep 1  # Quick Quiz: why is this needed?
	done
done

for ((nt = 1; nt <= $maxt; nt++))
do
	awk '{ print $2, $4/1000000. }' < smpalloc.$nt.dat > smpalloc-af.$nt.dat
done

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term pbm medium
set output "smpalloc.pbm"
set xlabel "Allocation Run Length"
set ylabel "Allocations/Frees Per Microsecond"
#set yrange [1:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "smpalloc-af.1.dat", "smpalloc-af.2.dat"
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "| ../../utilities/gnuplotepsfix > smpalloc.eps"
replot
---EOF---
ppmtogif smpalloc.pbm > smpalloc.gif 2> /dev/null
