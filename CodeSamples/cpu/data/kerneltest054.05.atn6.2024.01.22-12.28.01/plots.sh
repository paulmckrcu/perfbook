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

# For eps output
font=../../../../fonts/uhvr8a.pfb
fontsize=8
przsize="nosquare 0.55,0.25"

gnuplot << ---EOF---
set term postscript portrait color ${fontsize} enhanced fontfile "${font}" "NimbusSanL-Regu"
set size $przsize
set output "coe-nvals.eps"

set xlabel "Time (Timestamp Periods)"
set ylabel "Number of Simultaneous Values"
#set logscale y
set xrange [:10000]
#set yrange [100:10000]
set nokey
plot "coe-nvals.dat" w l
---EOF---

gnuplot << ---EOF---
set term postscript portrait color ${fontsize} enhanced fontfile "${font}" "NimbusSanL-Regu"
set size $przsize
set output "coe.eps"
stats "< perl expand.pl coe.dat" nooutput
N = STATS_records

set xlabel "Store-to-Store Latency (Timestamp Periods)"
set ylabel "Frequency (arb. unit)"
#set logscale y
set xrange [-2500:500]
set yrange [0:]
set nokey
#set border 3
set yzeroaxis
set boxwidth 1
set style fill solid 1.0 noborder
set xtics out
bin_width = 2
bin(x) = bin_width * floor(x/bin_width)
plot "< perl expand.pl coe.dat" using (bin(column(1))):(200./N) smooth frequency with boxes
---EOF---

gnuplot << ---EOF---
set term postscript portrait color ${fontsize} enhanced fontfile "${font}" "NimbusSanL-Regu"
set size $przsize
set output "fre.eps"
stats "< perl expand.pl fre.dat" nooutput
N = STATS_records

set xlabel "Load-to-Store Latency (Timestamp Periods)"
set ylabel "Frequency (arb. unit)"
#set logscale y
set xrange [-200:50]
set yrange [0:]
set nokey
set yzeroaxis
set boxwidth 1
set style fill solid 1.0 noborder
set xtics out
bin_width = 2
bin(x) = bin_width * floor(x/bin_width)
plot "< perl expand.pl fre.dat" using (bin(column(1))):(20./N) smooth frequency with boxes
---EOF---

gnuplot << ---EOF---
set term postscript portrait color ${fontsize} enhanced fontfile "${font}" "NimbusSanL-Regu"
set size $przsize
set output "rfe.eps"
stats "< perl expand.pl rfe.dat" nooutput
N = STATS_records

set xlabel "Store-to-Load Latency (Timestamp Periods)"
set ylabel "Frequency (arb. unit)"
#set logscale y
set xrange [0:350]
set yrange [0:]
set nokey
set yzeroaxis
set boxwidth 1
set style fill solid 1.0 noborder
set xtics out
bin_width = 2
bin(x) = bin_width * floor(x/bin_width)
plot "< perl expand.pl rfe.dat" using (bin(column(1))):(20./N) smooth frequency with boxes
---EOF---
