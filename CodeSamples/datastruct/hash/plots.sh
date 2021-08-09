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
# Copyright (C) IBM Corporation, 2013-2019
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
set output "perftest.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
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
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
# set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
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
set xlabel "Number of CPUs (Threads)"
set ylabel "Total Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "global" at 10,4000 left
set label 2 "bucket" at 5,30000 left
set label 3 "RCU,hazptr" at 17,130000 left
set label 4 "ideal" at 10,200000 right
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cpus.hash_bkt.${tag}.dat" w l, "zoo.cpus.hash_bkt_hazptr.${tag}.dat" w l, "zoo.cpus.hash_bkt_rcu.${tag}.dat" w l, "zoo.cpus.hash_global.${tag}.dat" w l, x*13963.9 w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocpulin.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Total Lookups per Millisecond"
#set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "bucket" at 30,60000 left
set label 2 "hazptr" at 30,300000 left
set label 3 "ideal" at 40,600000 right
set label 4 "RCU" at 50,530000 right
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cpus.hash_bkt.${tag}.dat" w l, "zoo.cpus.hash_bkt_hazptr.${tag}.dat" w l, "zoo.cpus.hash_bkt_rcu.${tag}.dat" w l, x*13963.9 w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocpubktlin8.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Total Lookups per Millisecond"
#set logscale xy
set xrange [1:8]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 5,61000 right
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cpus.hash_bkt.${tag}.dat" w l, 11201*x w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocpubktlin.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Total Lookups per Millisecond"
#set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cpus.hash_bkt.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocpubktsizelin.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Total Lookups per Millisecond"
#set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "1024" at 40,23000 left
set label 2 "2048" at 40,41800 left
set label 3 "4096" at 32,46000 left
set label 4 "8192" at 44,50000 left
set label 5 "16384" at 40,55000 left
plot "zoo.cpus.hash_bkt.${tag}.dat" w l, "zoo.cpus.hash_bkt-2048.${tag}.dat" w l, "zoo.cpus.hash_bkt-4096.${tag}.dat" w l, "zoo.cpus.hash_bkt-8192.${tag}.dat" w l, "zoo.cpus.hash_bkt-16384.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocatall.eps"
set xlabel "Number of CPUs (Threads) Looking Up The Cat"
set ylabel "Total Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
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
set xlabel "Number of CPUs (Threads) Looking Up The Cat"
set ylabel "Total Lookups per Millisecond"
#set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
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
set xlabel "Number of CPUs (Threads) Looking Up The Cat"
set ylabel "Cat Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "global" at 2,70 left
set label 2 "bucket" at 3,2000 left
set label 3 "hazptr" at 10,37000 left
set label 4 "RCU" at 10,150000 right
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cat.hash_bkt.${tag}.dat" w l, "zoo.cat.hash_bkt_hazptr.${tag}.dat" w l, "zoo.cat.hash_bkt_rcu.${tag}.dat" w l, "zoo.cat.hash_global.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoocatonlylin.eps"
set xlabel "Number of CPUs (Threads) Looking Up The Cat"
set ylabel "Cat Lookups per Millisecond"
#set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.cat.hash_bkt.${tag}.dat" w l, "zoo.cat.hash_bkt_hazptr.${tag}.dat" w l, "zoo.cat.hash_bkt_rcu.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zooupdatelu.eps"
set xlabel "Number of CPUs Doing Updates"
set ylabel "Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "global" at 10,300 right
set label 2 "bucket" at 3,20000 left
set label 3 "hazptr" at 5,100000 right
set label 4 "RCU" at 10,200000 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.updrd.hash_global.${tag}.dat" w l, "zoo.updrd.hash_bkt.${tag}.dat" w l, "zoo.updrd.hash_bkt_hazptr.${tag}.dat" w l, "zoo.updrd.hash_bkt_rcu.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zooupdatelulin.eps"
set xlabel "Number of CPUs Doing Updates"
set ylabel "Lookups per Millisecond"
set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.updrd.hash_global.${tag}.dat" w l, "zoo.updrd.hash_bkt.${tag}.dat" w l, "zoo.updrd.hash_bkt_hazptr.${tag}.dat" w l, "zoo.updrd.hash_bkt_rcu.${tag}.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zooupdate.eps"
set xlabel "Number of CPUs Doing Updates"
set ylabel "Updates per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "global" at 10,60 left
set label 2 "bucket" at 60,33000 right
set label 3 "RCU" at 30,3000 left
set label 4 "hazptr" at 10,13000 right
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.upd.hash_global.${tag}.dat" w l, "zoo.upd.hash_bkt.${tag}.dat" w l, "zoo.upd.hash_bkt_hazptr.${tag}.dat" w l, "zoo.upd.hash_bkt_rcu.${tag}.dat" w l
---EOF---
