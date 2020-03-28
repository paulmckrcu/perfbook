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
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "rwlockscale.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Critical Section Performance"
set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "ideal" at 200,1.5 left
set label 2 "1000us" at 350,0.28 left
set label 3 "100us" at 350,0.05 left
set label 4 "10us" at 350,0.007 left
set label 5 "1us" at 350,0.00055 left
# set label 5 "100K" at 120,0.1 left
# set label 6 "10K" at 20,0.2 left
# set label 7 "1K" at 18,0.03 right
plot "rwlockscale.hps.2020.03.25a.dat" w e, "rwlockscale.hps.2020.03.25a.dat" w l, 1
---EOF---
