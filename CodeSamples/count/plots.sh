#! /bin/sh
#
# Create plots from the counting test programs.
#
# Execute this script in the current directory.
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

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > atomic.eps"
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
plot "data/count_atomic:u.2009.05.03a.dat" w e, "data/count_atomic:u.2009.05.03a.dat" w l, 8.81772
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > atomic125.eps"
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
plot "data/count_atomic\:u.2009.05.25a.dat" w e, "data/count_atomic\:u.2009.05.25a.dat" w l, 8.81772
set term png medium
set output "atomic125.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > atomic_nehalem.eps"
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
plot "data/count_atomic:u.elm3b128.2009.05.29a.dat" w e, "data/count_atomic:u.elm3b128.2009.05.29a.dat" w l
set term png medium
set output "atomic_nehalem.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > atomic_hps.eps"
set xlabel "Number of CPUs (Threads)"
set xtics rotate
set ylabel "Time Per Increment (ns)"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
plot "data/count_atomic:u.hps.2019.10.23a.dat" w e, "data/count_atomic:u.hps.2019.10.23a.dat" w l, 1.46041
set term png medium
set output "atomic_hps.png"
replot
---EOF---
