#! /bin/sh
#
# Create plots for the SMPdesign directory.
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
# Copyright (C) IBM Corporation, 2009
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../utilities/gnuplotepsfix > clockfreq.eps"
set xlabel "Year"
set ylabel "CPU Clock Frequency / MIPS"
set logscale y
#set yrange [1:10000]
set yrange [0.1:10000]
set nokey
set xtics rotate
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
#plot "clockfreq.dat", "clockfreqP4.dat", "clockfreqP3.dat"
plot "clockfreq80x86.dat", "clockfreqPPro.dat", "clockfreqP1.dat", "clockfreqP2.dat", "clockfreqP3.dat", "clockfreqP4.dat", "clockfreqXeonDC.dat", "clockfreqAtom.dat", "clockfreqNehalem.dat", "clockfreqSandyBridge.dat", "clockfreqIvyBridge.dat", "clockfreqHaswell.dat", "clockfreqBroadwell.dat", "clockfreqSkylake.dat"
# plot "clockfreqP4.dat", "clockfreqP3.dat", "clockfreqP2.dat"
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../utilities/gnuplotepsfix > CPUvsEnet.eps"
set xlabel "Year"
set ylabel "Relative Performance"
set logscale y
#set yrange [1:10000]
set yrange [0.1:1000000]
set nokey
set xtics rotate
set label 1 "Ethernet" at 2009,70000 right
set label 2 "x86 CPUs" at 2001,100 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
#plot "clockfreq.dat", "clockfreqP4.dat", "clockfreqP3.dat"
plot "enet.dat" w l, "clockfreq80x86.dat", "clockfreqPPro.dat", "clockfreqP1.dat", "clockfreqP2.dat", "clockfreqP3.dat", "clockfreqP4.dat", "clockfreqXeonDC.dat", "clockfreqAtom.dat", "clockfreqNehalem.dat", "clockfreqSandyBridge.dat", "clockfreqIvyBridge.dat", "clockfreqHaswell.dat", "clockfreqBroadwell.dat", "clockfreqSkylake.dat"
# plot "clockfreqP4.dat", "clockfreqP3.dat", "clockfreqP2.dat"
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "../fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|../utilities/gnuplotepsfix > mipsperbuck.eps"
set xlabel "Year"
set ylabel "MIPS per Die"
set logscale y
#set yrange [1:10000]
# set yrange [0.1:1000000]
set nokey
set xtics rotate
# set label 1 "Ethernet" at 2009,70000 right
# set label 2 "x86 CPUs" at 2001,100 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "mipsperbuck.dat"
# plot "clockfreqP4.dat", "clockfreqP3.dat", "clockfreqP2.dat"
---EOF---

gnuplot << ---EOF---
set term gif
set size square ${plotsize},${plotsize}
set output "synceff.gif"
set xlabel "Number of CPUs (Threads)"
set ylabel "Synchronization Efficiency"
#set logscale y
set yrange [.1:1]
set xrange [1:100]
set nokey
set xtics rotate
set label 1 "10" at 12,0.2 left
set label 2 "25" at 27,0.3 left
set label 3 "50" at 52,0.4 left
set label 4 "75" at 76,0.5 left
set label 5 "100" at 96,0.65 right
eff(f,n)=(f-n)/(f-(n-1.))
plot eff(10,x), eff(25,x), eff(50,x), eff(75,x), eff(100,x)
set term postscript portrait enhanced "NimbusSanL-Regu" fontfile "../fonts/uhvr8a.pfb"
set output "|../utilities/gnuplotepsfix > synceff.eps"
replot
---EOF---

gnuplot << ---EOF---
set term gif
set size square ${plotsize},${plotsize}
set output "matmuleff.gif"
set xlabel "Number of CPUs (Threads)"
set ylabel "Matrix Multiply Efficiency"
set logscale x
set xrange [1:100]
set nokey
set label 1 "64" at 3.5,0.4 right
set label 2 "128" at 3.8,0.72 right
set label 3 "256" at 17,0.68 right
set label 4 "512" at 75,0.58 right
set label 5 "1024" at 90,0.93 right
plot "matmul.sh.2010.03.28a.dat" w l, "matmul.sh.2010.03.28a.dat" w l
set term postscript portrait enhanced "NimbusSanL-Regu" fontfile "../fonts/uhvr8a.pfb"
set output "|../utilities/gnuplotepsfix > matmuleff.eps"
replot
---EOF---
