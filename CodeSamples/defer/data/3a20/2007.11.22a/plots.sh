#! /bin/sh

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term pbm medium
set output "rwlockRCUperfPREEMPT.pbm"
set xlabel "Number of CPUs"
set ylabel "Overhead (nanoseconds)"
set data style lines
set nokey
set logscale y
set label 1 "RCU" at 15,9 right
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
set label 4 "rwlock" at 15,3400 right
# set label 5 "refcnt" at 0.15,2.8 left
plot "RCUperfPREEMPTerr.dat", "RCUperfPREEMPTerr.dat" w e, "rwlockperfPREEMPTerr.dat" w errorbars, "rwlockperfPREEMPTerr.dat" w l
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|gnuplotepsfixdc > rwlockRCUperfPREEMPT.eps"
replot
---EOF---
convert rwlockRCUperfPREEMPT.pbm rwlockRCUperfPREEMPT.jpg

gnuplot << ---EOF---
set term pbm medium
set output "refRCUperfPREEMPT.pbm"
set xlabel "Number of CPUs"
set ylabel "Overhead (nanoseconds)"
set data style lines
set nokey
set logscale y
set label 1 "RCU" at 15,9 right
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 15,4000 right
set label 5 "refcnt" at 15,1500 right
plot "RCUperfPREEMPT.dat", "RCUperfPREEMPTerr.dat" w e, "atomicrefperfPREEMPTerr.dat" w errorbars, "atomicrefperfPREEMPTerr.dat" w l
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|gnuplotepsfixdc > refRCUperfPREEMPT.eps"
replot
---EOF---
convert refRCUperfPREEMPT.pbm refRCUperfPREEMPT.jpg
