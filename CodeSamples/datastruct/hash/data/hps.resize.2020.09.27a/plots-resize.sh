#! /bin/sh
#
# Create plots from the hash-table test programs for resizable hash tables.
#
# Usage: sh plots-resize.sh tag perfbook-path
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

tag=${1-hps.2020.09.05a}
font=${2-../../../../..}/

fontsize=10
plotsize=0.5

cp ../hps.resize.2020.09.05a/*.dat .

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "perftestresizebig.eps"
set xlabel "Number of CPUs (Threads)"
set ylabel "Lookups per Millisecond"
set logscale xy
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
set label 1 "262,144" at 13,5e5 right
set label 2 "2,097,152" at 10,8000 left
# set label 3 "131,072" at 10,5000 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "perftestS.2097152.${tag}.dat" dt 2 w l,\
     "perftestR.2097152.${tag}.dat" dt 1 w l,\
     "perftestL.2097152.${tag}.dat" dt 3 w l,\
     "perftestS.262144.${tag}.dat" dt 2 w l,\
     "perftestR.262144.${tag}.dat" dt 1 w l,\
     "perftestL.262144.${tag}.dat" dt 3 w l,\
     "perftestL.2097152.hps.2020.09.27a.dat" dt 7 w l
---EOF---
