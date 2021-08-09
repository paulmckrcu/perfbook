#! /bin/sh
#
# Create plots from the counting test programs.
#
#	Usage: sh plots.sh <tag>
#
# For example, "sh plots.sh 2014.09.09b".
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
# Copyright (C) IBM Corporation, 2009-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

for i in lookup data data-moves
do
	sh reduce.sh < $i.$1.txt | grep '^[0-9]' | sort -k1n > $i.$1.dat
done

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "/home/git/perfbook/fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|/home/git/perfbook/utilities/gnuplotepsfix > lookup.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups Per Millisecond"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "lookup.$1.dat" w e, "lookup.$1.dat" w l, 0
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "/home/git/perfbook/fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|/home/git/perfbook/utilities/gnuplotepsfix > ops.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Operations Per Millisecond"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "data.$1.dat" w e, "data.$1.dat" w l, 0
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "/home/git/perfbook/fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|/home/git/perfbook/utilities/gnuplotepsfix > moves-8.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Moves Per Millisecond"
#set logscale y
set xrange [0:8]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "data-moves.$1.dat" w e, "data-moves.$1.dat" w l, 0
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "/home/git/perfbook/fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|/home/git/perfbook/utilities/gnuplotepsfix > moves.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Moves Per Millisecond"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "data-moves.$1.dat" w e, "data-moves.$1.dat" w l, 0
---EOF---

