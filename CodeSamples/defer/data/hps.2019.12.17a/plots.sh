#! /bin/sh
#
# Create plots from the pre-BSD test programs.
#
# Usage: sh plots.sh tag perfbook-path
#
# Execute this script in the directory containing the data.
# The tag is the same string passed to reduce.sh.  The perfbook-path
# is the path to the top-level perfbook directory, defaulting to ../../.
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

tag=$1
font=${2-../../../../}

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perf-refcnt.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 300,1.9e7 right
set label 2 "refcnt" at 330,1.5e6 right
# set label 3 "hazptr" at 360,3.5e6 left
# set label 4 "seqlock" at 250,5.6e6 right
# set label 5 "RCU" at 400,1.4e7 right
plot "route_seq.$tag.dat" w l, "route_seq.$tag.dat" w e, "route_refcnt.$tag.dat" w l, "route_refcnt.$tag.dat" w e
---EOF---
# cp perf-refcnt.eps ../..

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perf-refcnt-logscale.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 100,1.8e7 right
set label 2 "refcnt" at 10,7000 right
# set label 3 "hazptr" at 360,3.5e6 left
# set label 4 "seqlock" at 250,5.6e6 right
# set label 5 "RCU" at 400,1.4e7 right
plot "route_seq.$tag.dat" w l, "route_seq.$tag.dat" w e, "route_refcnt.$tag.dat" w l, "route_refcnt.$tag.dat" w e
---EOF---
# cp perf-refcnt-logscale.eps ../..

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perf-hazptr.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 300,1.9e7 right
# set label 2 "refcnt" at 330,1.5e6 right
set label 3 "hazptr" at 360,3.5e6 left
# set label 4 "seqlock" at 250,5.6e6 right
# set label 5 "RCU" at 400,1.4e7 right
plot "route_seq.$tag.dat" w l, "route_seq.$tag.dat" w e, "route_hazptr.$tag.dat" w l, "route_hazptr.$tag.dat" w e
---EOF---
# cp perf-hazptr.eps ../..

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perf-seqlock.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 300,1.9e7 right
# set label 2 "refcnt" at 330,1.5e6 right
set label 3 "hazptr" at 360,3.5e6 left
set label 4 "seqlock" at 250,5.6e6 right
# set label 5 "RCU" at 400,1.4e7 right
plot "route_seq.$tag.dat" w l, "route_seq.$tag.dat" w e, "route_hazptr.$tag.dat" w l, "route_hazptr.$tag.dat" w e, "route_seqlock.$tag.dat" w l, "route_seqlock.$tag.dat" w e
---EOF---
# cp perf-seqlock.eps ../..

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perf-rcu.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 300,1.9e7 right
# set label 2 "refcnt" at 330,1.5e6 right
set label 3 "hazptr" at 360,3.5e6 left
set label 4 "seqlock" at 250,5.6e6 right
set label 5 "RCU" at 400,1.4e7 right
plot "route_seq.$tag.dat" w l, "route_seq.$tag.dat" w e, "route_hazptr.$tag.dat" w l, "route_hazptr.$tag.dat" w e, "route_seqlock.$tag.dat" w l, "route_seqlock.$tag.dat" w e, "route_rcu.$tag.dat" w l, "route_rcu.$tag.dat" w e
---EOF---
# cp perf-rcu.eps ../..

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perf-rcu-qsbr.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 350,2e7 right
# set label 2 "refcnt" at 330,1.5e6 right
set label 3 "hazptr" at 360,3.5e6 left
set label 4 "seqlock" at 250,5.6e6 right
set label 5 "RCU" at 400,1.4e7 right
# set label 6 "RCU-QSBR" at 300,2e7 right
plot "route_seq.$tag.dat" w l, "route_seq.$tag.dat" w e, "route_hazptr.$tag.dat" w l, "route_hazptr.$tag.dat" w e, "route_seqlock.$tag.dat" w l, "route_seqlock.$tag.dat" w e, "route_rcu.$tag.dat" w l, "route_rcu.$tag.dat" w e, "route_rcu_qsbr.$tag.dat" w l, "route_rcu_qsbr.$tag.dat" w e
---EOF---
# cp perf-rcu-qsbr.eps ../../perf-rcu-qsbr-qq.eps
