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
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright (C) IBM Corporation, 2009-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > HTMovf4K.eps"
set xlabel "Transaction Footprint in Cache Lines (4K)"
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
set xlabel "Transaction Footprint in Cache Lines (4K)"
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

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > HTMovf32KMC.eps"
set xlabel "Transaction Footprint in Cache Lines (32K)"
set ylabel "Probability of Transaction Overflow"
set logscale xy
set nokey
set yrange [0.0001:1]
set label 1 "DM" at 3.2,0.01 right
set label 2 "2-way" at 9,0.002 right
set label 3 "4-way" at 28,0.0005 right
set label 4 "8-way" at 87,2e-4 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "HTMovfMCNK.bash.32K.1.64.out" w l, "HTMovfMCNK.bash.32K.2.64.out" w l, "HTMovfMCNK.bash.32K.4.64.out" w l, "HTMovfMCNK.bash.32K.8.64.out" w l
set term png small crop
set output "HTMovf32KMC.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > HTMovfx86MC.eps"
set xlabel "Transaction Footprint in Cache Lines (x86)"
set ylabel "Probability of Transaction Overflow"
set logscale xy
set nokey
set yrange [0.0001:1]
set label 1 "DM" at 3.2,0.1 right
set label 2 "2-way" at 7.3,0.013 right
set label 3 "4-way" at 20,0.001 right
set label 4 "8-way" at 95,3e-4 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "HTMovfMCNK.bash.4K.1.64.out" w l, "HTMovfMCNK.bash.8K.2.64.out" w l, "HTMovfMCNK.bash.16K.4.64.out" w l, "HTMovfMCNK.bash.32K.8.64.out" w l
set term png small crop
set output "HTMovfx86MC.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > HTMovfx86SMC.eps"
set xlabel "Transaction Footprint in Cache Lines (x86)"
set ylabel "Probability of Transaction Overflow"
set logscale xy
set nokey
set yrange [0.01:1]
set label 1 "64-byte" at 9,0.7 right
set label 2 "32-byte" at 3.5,0.02 left
# set label 3 "4-way" at 20,0.001 right
# set label 4 "8-way" at 95,3e-4 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "HTMovfMCNK.bash.4K.1.32.out" w l, "HTMovfMCNK.bash.4K.1.64.out" w l
set term png small crop
set output "HTMovfx86SMC.png"
replot
---EOF---
