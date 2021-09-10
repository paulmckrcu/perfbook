#! /bin/sh

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term pbm medium
set output "rwlockRCUperfwtPREEMPT.pbm"
set xlabel "Critical-Section Duration (microseconds)"
set ylabel "Overhead (nanoseconds)"
set data style lines
set nokey
# set logscale y
set xrange [0:10]
set label 1 "RCU" at 3,2000 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
set label 4 "rwlock" at 1,7500 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "RCUperfwtPREEMPTerr.dat", "RCUperfwtPREEMPTerr.dat" w e, "rwlockperfwtPREEMPTerr.dat", "rwlockperfwtPREEMPTerr.dat" w e
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|gnuplotepsfixdc > rwlockRCUperfwtPREEMPT.eps"
replot
---EOF---
convert rwlockRCUperfwtPREEMPT.pbm rwlockRCUperfwtPREEMPT.jpg

gnuplot << ---EOF---
set term pbm medium
set output "refRCUperfwtPREEMPT.pbm"
set xlabel "Critical-Section Duration (microseconds)"
set ylabel "Overhead (nanoseconds)"
set data style lines
set nokey
# set logscale y
set xrange [0:10]
set label 1 "RCU" at 3,2000 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 15,4000 right
set label 5 "refcnt" at 0.5,3700 left
plot "RCUperfwtPREEMPTerr.dat", "RCUperfwtPREEMPTerr.dat" w e, "atomicrefperfwtPREEMPTerr.dat", "atomicrefperfwtPREEMPTerr.dat" w e
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|gnuplotepsfixdc > refRCUperfwtPREEMPT.eps"
replot
---EOF---
convert refRCUperfwtPREEMPT.pbm refRCUperfwtPREEMPT.jpg
