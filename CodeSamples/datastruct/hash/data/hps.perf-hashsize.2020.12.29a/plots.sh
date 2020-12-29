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

tag=${1-hps.2020.11.26a}
font=${2-../../../../../}

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "zoohashsize.eps"
set xlabel "Hash Table Size (Buckets and Maximum Elements)"
set ylabel "Total Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set xtics rotate by 90 right
set nokey
set label 1 "ideal" at 200000,1.5e7 left
set label 2 "unsync" at 5e6,5e6 right
set label 3 "QSBR,RCU,hazptr" at 400000,1e6 right
# set label 4 "unsync" at 250,5000000 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "zoo.hashsize.hash_bkt_hazptr.${tag}.dat" w l, "zoo.hashsize.hash_bkt_qsbr.${tag}.dat" w l, "zoo.hashsize.hash_bkt_rcu.${tag}.dat" w l, "zoo.hashsize.hash_unsync.${tag}.dat" w l, 1.04207e+07 w l
---EOF---
