#!/bin/sh
#
# Plot reduced temporal coe data.
#
# Usage: sh plots.sh
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
# Copyright (C) Meta Platforms Inc., 2024
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

gnuplot << ---EOF---
set term png
set output "coe-nvals.png"
set xlabel "Time (Timestamp Periods)"
set ylabel "Number of Simultaneous Values"
#set logscale y
set xrange [:20000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "coe-nvals.dat" w l
---EOF---

gnuplot << ---EOF---
set term png
set output "coe.png"
set xlabel "Store-to-Store Latency (Timestamp Periods)"
set ylabel "Number of Samples"
#set logscale y
set xrange [-2500:500]
set yrange [0:]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "coe.dat" w points pt 6 pointsize 0.2
---EOF---

gnuplot << ---EOF---
set term png
set output "fre.png"
set xlabel "Load-to-Store Latency (Timestamp Periods)"
set ylabel "Number of Samples"
#set logscale y
set xrange [-250:100]
set yrange [0:]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "fre.dat" w points pt 6 pointsize 0.5
---EOF---

gnuplot << ---EOF---
set term png
set output "rfe.png"
set xlabel "Store-to-Load Latency (Timestamp Periods)"
set ylabel "Number of Samples"
#set logscale y
set xrange [0:350]
set yrange [0:]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "rfe.dat" w points pt 6 pointsize 0.5
---EOF---
