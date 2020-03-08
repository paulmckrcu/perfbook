#! /bin/sh
#
# Create plots from the cachetorture script.
#
# Usage: sh plots.sh tag perfbook-path
#
# Execute this script in the directory containing the data.
# The tag is the same string passed to reduce.sh.  The perfbook-path
# is the path to the top-level perfbook directory, defaulting to
# ../../../../.
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

tag=$1
font=${2-../../../../}

fontsize=8
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "cachetorture-latency.eps"
set xlabel "Hardware Thread (CPU) Number"
set ylabel "Nanoseconds per Operation"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "cmpxchg 1" at 40,420 left
set label 2 "cmpxchg 2" at 120,800 left
set label 3 "atomic inc" at 120,750 left
set label 4 "write" at 120,700 left
set label 5 "local lock" at 400,120 right
set label 6 "local cmpxchg" at 400,70 right
plot "${tag}.atomicinc.dat" w l, "${tag}.blindcmpxchg.dat" w l, "${tag}.cmpxchg.dat" w l, "${tag}.write.dat" w l, 7.0862, 15.479
set term jpeg large
set size square 1.0,1.0
set output "cachetorture-latency.jpg
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "cachetorture-latency-scatter.eps"
set xlabel "Hardware Thread (CPU) Number"
set ylabel "Nanoseconds per Operation"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "blind" at 40,490 left
set label 2 "cmpxchg" at 40,430 left
set label 3 "cmpxchg" at 120,750 left
set label 5 "local lock" at 400,120 right
set label 6 "local cmpxchg" at 400,70 right
plot "${tag}.blindcmpxchg.sctr.dat" w p pt 0, "${tag}.cmpxchg.sctr.dat" w p pt 0, "${tag}.blindcmpxchg.dat" w l, "${tag}.cmpxchg.dat" w l, 7.0862, 15.479
set term jpeg large
set size square 1.0,1.0
set output "cachetorture-latency-scatter.jpg
replot
---EOF---
# cp perf-refcnt.eps ../..
# cp perf-refcnt.eps ../..
