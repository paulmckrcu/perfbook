#! /bin/sh
#
# Create plots from the hash-table test programs.
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
set label 1 "ideal" at 6.9,400000 right
set label 2 "refcnt" at 7.8,30000 right
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "route_seq.paulmck.2016.07.07a.dat" w l, "route_seq.paulmck.2016.07.07a.dat" w e, "route_refcnt.paulmck.2016.07.07a.dat" w l, "route_refcnt.paulmck.2016.07.07a.dat" w e
---EOF---
# cp perf-refcnt.eps ../..

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
set label 1 "ideal" at 6.9,400000 right
set label 2 "refcnt" at 7.8,32000 right
set label 3 "hazptr" at 5,48000 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "route_seq.paulmck.2016.07.07a.dat" w l, "route_seq.paulmck.2016.07.07a.dat" w e, "route_refcnt.paulmck.2016.07.07a.dat" w l, "route_refcnt.paulmck.2016.07.07a.dat" w e, "route_hazptr.paulmck.2016.07.07a.dat" w l, "route_hazptr.paulmck.2016.07.07a.dat" w e
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
set label 1 "ideal" at 6.9,400000 right
set label 2 "refcnt" at 7.8,32000 right
set label 3 "hazptr" at 5,48000 left
set label 4 "seqlock" at 7.8,165000 right
# set label 5 "refcnt" at 0.15,2.8 left
plot "route_seq.paulmck.2016.07.07a.dat" w l, "route_seq.paulmck.2016.07.07a.dat" w e, "route_refcnt.paulmck.2016.07.07a.dat" w l, "route_refcnt.paulmck.2016.07.07a.dat" w e, "route_hazptr.paulmck.2016.07.07a.dat" w l, "route_hazptr.paulmck.2016.07.07a.dat" w e, "route_seqlock.paulmck.2016.07.07a.dat" w l, "route_seqlock.paulmck.2016.07.07a.dat" w e
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
set label 1 "ideal" at 6.9,400000 right
set label 2 "refcnt" at 7.8,32000 right
set label 3 "hazptr" at 5,48000 left
set label 4 "seqlock" at 7.8,165000 right
set label 5 "RCU" at 7.8,286000 right
plot "route_seq.paulmck.2016.07.07a.dat" w l, "route_seq.paulmck.2016.07.07a.dat" w e, "route_refcnt.paulmck.2016.07.07a.dat" w l, "route_refcnt.paulmck.2016.07.07a.dat" w e, "route_hazptr.paulmck.2016.07.07a.dat" w l, "route_hazptr.paulmck.2016.07.07a.dat" w e, "route_seqlock.paulmck.2016.07.07a.dat" w l, "route_seqlock.paulmck.2016.07.07a.dat" w e, "route_rcu.paulmck.2016.07.07a.dat" w l, "route_rcu.paulmck.2016.07.07a.dat" w e
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
set label 1 "ideal" at 6.9,400000 right
set label 2 "refcnt" at 7.8,32000 right
set label 3 "hazptr" at 5,48000 left
set label 4 "seqlock" at 7.8,165000 right
set label 5 "RCU" at 7.8,286000 right
plot "route_seq.paulmck.2016.07.07a.dat" w l, "route_seq.paulmck.2016.07.07a.dat" w e, "route_refcnt.paulmck.2016.07.07a.dat" w l, "route_refcnt.paulmck.2016.07.07a.dat" w e, "route_hazptr.paulmck.2016.07.07a.dat" w l, "route_hazptr.paulmck.2016.07.07a.dat" w e, "route_seqlock.paulmck.2016.07.07a.dat" w l, "route_seqlock.paulmck.2016.07.07a.dat" w e, "route_rcu.paulmck.2016.07.07a.dat" w l, "route_rcu.paulmck.2016.07.07a.dat" w e, "route_rcu_qsbr.paulmck.2016.07.12a.dat" w l, "route_rcu_qsbr.paulmck.2016.07.12a.dat" w e
---EOF---
# cp perf-rcu-qsbr.eps ../..
