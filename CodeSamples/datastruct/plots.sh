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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
#
# Copyright (C) IBM Corporation, 2013
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

tag=$1
font=${2-../../}

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perftest.eps"
set xlabel "Number of CPUs/Threads"
set ylabel "Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "perftest.hash_bkt.${tag}.dat" w l, "perftest.hash_bkt_hazptr.${tag}.dat" w l, "perftest.hash_bkt_rcu.${tag}.dat" w l, "perftest.hash_global.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perftestlin.eps"
set xlabel "Number of CPUs/Threads"
set ylabel "Lookups per Millisecond"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "perftest.hash_bkt.${tag}.dat" w l, "perftest.hash_bkt_hazptr.${tag}.dat" w l, "perftest.hash_bkt_rcu.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocpu.eps"
set xlabel "Number of CPUs/Threads"
set ylabel "Total Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cpus.hash_bkt.${tag}.dat" w l, "zoo.cpus.hash_bkt_hazptr.${tag}.dat" w l, "zoo.cpus.hash_bkt_rcu.${tag}.dat" w l, "zoo.cpus.hash_global.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocpulin.eps"
set xlabel "Number of CPUs/Threads"
set ylabel "Total Lookups per Millisecond"
#set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cpus.hash_bkt.${tag}.dat" w l, "zoo.cpus.hash_bkt_hazptr.${tag}.dat" w l, "zoo.cpus.hash_bkt_rcu.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocatall.eps"
set xlabel "Number of CPUs/Threads Looking Up The Cat"
set ylabel "Total Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.catall.hash_bkt.${tag}.dat" w l, "zoo.catall.hash_bkt_hazptr.${tag}.dat" w l, "zoo.catall.hash_bkt_rcu.${tag}.dat" w l, "zoo.catall.hash_global.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocatalllin.eps"
set xlabel "Number of CPUs/Threads Looking Up The Cat"
set ylabel "Total Lookups per Millisecond"
#set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.catall.hash_bkt.${tag}.dat" w l, "zoo.catall.hash_bkt_hazptr.${tag}.dat" w l, "zoo.catall.hash_bkt_rcu.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocatonly.eps"
set xlabel "Number of CPUs/Threads Looking Up The Cat"
set ylabel "Cat Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cat.hash_bkt.${tag}.dat" w l, "zoo.cat.hash_bkt_hazptr.${tag}.dat" w l, "zoo.cat.hash_bkt_rcu.${tag}.dat" w l, "zoo.cat.hash_global.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocatonlylin.eps"
set xlabel "Number of CPUs/Threads Looking Up The Cat"
set ylabel "Cat Lookups per Millisecond"
#set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cat.hash_bkt.${tag}.dat" w l, "zoo.cat.hash_bkt_hazptr.${tag}.dat" w l, "zoo.cat.hash_bkt_rcu.${tag}.dat" w l
---EOF---
