#! /bin/sh
#
# Create plots from the counting test programs.
#
# Execute this script in the current directory.
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
# Copyright (C) IBM Corporation, 2009
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > HTMovf4K.eps"
set xlabel "Transaction Footprint in Cache Lines"
set ylabel "Probability of Transaction Overflow"
set logscale xy
set nokey
set label 1 "DM" at 3.2,0.1 right
set label 2 "2-way" at 4.6,0.01 right
set label 3 "4-way" at 7.8,0.001 right
set label 4 "8-way" at 11.6,1e-6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "HTMovfNK.bash.4K.1.64.out" w l, "HTMovfNK.bash.4K.2.64.out" w l, "HTMovfNK.bash.4K.4.64.out" w l, "HTMovfNK.bash.4K.8.64.out" w l
set term png small crop
set output "HTMovf4K.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > HTMovf4KMC.eps"
set xlabel "Transaction Footprint in Cache Lines"
set ylabel "Probability of Transaction Overflow"
set logscale xy
set nokey
set label 1 "DM" at 3.2,0.1 right
set label 2 "2-way" at 4.6,0.01 right
set label 3 "4-way" at 7.8,0.001 right
set label 4 "8-way" at 11.6,1e-6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "HTMovfNK.bash.4K.1.64.out" w l, "HTMovfNK.bash.4K.2.64.out" w l, "HTMovfNK.bash.4K.4.64.out" w l, "HTMovfNK.bash.4K.8.64.out" w l, "HTMovfMCNK.bash.4K.1.64.out", "HTMovfMCNK.bash.4K.2.64.out", "HTMovfMCNK.bash.4K.4.64.out", "HTMovfMCNK.bash.4K.8.64.out"
set term png small crop
set output "HTMovf4KMC.png"
replot
---EOF---
