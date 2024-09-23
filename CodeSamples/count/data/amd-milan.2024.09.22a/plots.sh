#! /bin/sh
#
# Create plots from the counting test programs.
#
# Execute this script in the directory containing the data.
#
# Usage: sh plots.sh <tag>
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
# Copyright (C) Facebook, 2024
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

tag=${1-amd-milan.2024.09.22a}

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "atomic.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Time Per Increment (nanoseconds)"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "count_atomic:u.${tag}.dat" w e, "count_atomic:u.${tag}.dat" w l, 0.694145
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "count_end-u.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Time Per Increment (ns)"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "count_end:u.${tag}.dat" w e, "count_end:u.${tag}.dat" w l, 0.694145
set term png medium
set output "count_end-u.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "count_end-r.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Time Per Increment (ns)"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "count_end:r.${tag}.dat" w e, "count_end:r.${tag}.dat" w l, 0.351683
set term png medium
set output "count_end-r.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "count_stat_eventual-u.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Time Per Increment (ns)"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "count_stat_eventual:u.${tag}.dat" w e, "count_stat_eventual:u.${tag}.dat" w l, 0.694145
set term png medium
set output "count_stat_eventual-u.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "count_stat_eventual-r.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Time Per Increment (ns)"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "count_stat_eventual:r.${tag}.dat" w e, "count_stat_eventual:r.${tag}.dat" w l, 0.351683
set term png medium
set output "count_stat_eventual-r.png"
replot
---EOF---
