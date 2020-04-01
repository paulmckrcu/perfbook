#! /bin/sh
#
# Create matrix-multiply efficiency for the SMPdesign directory.
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

fontsize=8
plotsize=0.5

gnuplot << ---EOF---
set size square ${plotsize},${plotsize}
set term postscript portrait enhanced "NimbusSanL-Regu" fontfile "../../../../fonts/uhvr8a.pfb"
set output "matmuleff.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Matrix Multiply Efficiency"
set logscale x
# set xrange [1:100]
set nokey
set label 1 "64" at 1.9,0.07 right
set label 2 "128" at 2.8,0.47 right
set label 3 "256" at 2.8,0.80 right
set label 4 "512" at 55,0.47 right
set label 5 "1024" at 150,0.88 right
plot "matmul.hps.2020.03.30a.dat" w l, "matmul.hps.2020.03.30a.dat" w e, 1.0
---EOF---
