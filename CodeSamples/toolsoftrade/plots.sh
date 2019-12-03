#! /bin/sh
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
plotsize=0.7

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix.7 > rwlockscale.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Critical Section Performance"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 120,0.97 left
set label 2 "100M" at 120,0.67 left
set label 3 "10M" at 120,0.52 left
set label 4 "1M" at 120,0.27 left
set label 5 "100K" at 120,0.1 left
set label 6 "10K" at 20,0.2 left
set label 7 "1K" at 18,0.03 right
plot "data/rwlockscale.dat" w e, "data/rwlockscale.dat" w l, 1
---EOF---
