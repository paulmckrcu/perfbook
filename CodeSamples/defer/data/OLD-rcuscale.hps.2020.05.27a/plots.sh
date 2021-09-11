#! /bin/sh
#
# Create plots from the rcuscale test data.
#
# Usage: sh plots.sh tag perfbook-path
#
# Execute this script in the directory containing the data.  The tag is
# the same string passed to reduce_rcuscale.sh.  The perfbook-path is the
# path to the top-level perfbook directory, defaulting to ../../../../.
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

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "rwlockRCUperf.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Nanoseconds per operation"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "RCU" at 30,1.7 left
set label 2 "rwlock" at 4,650 left
# set label 3 "hazptr" at 360,3.5e6 left
# set label 4 "seqlock" at 250,5.6e6 right
# set label 5 "RCU" at 400,1.4e7 right
plot "rcu-eb.$tag.dat" w l, "rcu-eb.$tag.dat" w e, "rwlock-eb.$tag.dat" w l, "rwlock-eb.$tag.dat" w e
---EOF---
# cp rwlockRCUperf.eps ../../../../defer

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "rwlockRCUperf-pc.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Nanoseconds per operation"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "RCU" at 30,1.7 left
set label 2 "rwlock" at 4,500 left
# set label 3 "hazptr" at 360,3.5e6 left
# set label 4 "seqlock" at 250,5.6e6 right
# set label 5 "RCU" at 400,1.4e7 right
plot "rcu-points.$tag.dat" w points pt "#", "rwlock-points.$tag.dat" w points pt "#"
---EOF---
# cp perf-refcnt.eps ../..

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "refcntRCUperf.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Nanoseconds per operation"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "RCU" at 30,1.7 left
set label 2 "refcnt" at 4,450 left
# set label 3 "hazptr" at 360,3.5e6 left
# set label 4 "seqlock" at 250,5.6e6 right
# set label 5 "RCU" at 400,1.4e7 right
plot "rcu-eb.$tag.dat" w l, "rcu-eb.$tag.dat" w e, "refcnt-eb.$tag.dat" w l, "refcnt-eb.$tag.dat" w e
---EOF---
# cp refcntRCUperf.eps ../../../../defer

exit 0

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
