#! /bin/sh

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term pbm medium
set output "rwlockRCUperfdbg.pbm"
set xlabel "Number of CPUs"
set ylabel "Overhead (nanoseconds)"
set data style lines
set nokey
set logscale y
set label 1 "RCU" at 7.5,27 right
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
set label 4 "rwlock" at 7.5,3000 right
# set label 5 "refcnt" at 0.15,2.8 left
plot "RCUperfdbg.dat", "rwlockperfdbg.dat"
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|gnuplotepsfixdc > rwlockRCUperfdbg.eps"
replot
---EOF---
convert rwlockRCUperfdbg.pbm rwlockRCUperfdbg.jpg

gnuplot << ---EOF---
set term pbm medium
set output "rwlockRCUperf.pbm"
set xlabel "Number of CPUs"
set ylabel "Overhead (nanoseconds)"
set data style lines
set nokey
set logscale y
set label 1 "RCU" at 15,0.0007 right
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
set label 4 "rwlock" at 15,1000 right
# set label 5 "refcnt" at 0.15,2.8 left
plot "RCUperfnonPREEMPTerr.dat", "RCUperfnonPREEMPTerr.dat" w e, "rwlockperfnonPREEMPTerr.dat", "rwlockperfnonPREEMPTerr.dat" w e
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|gnuplotepsfixdc > rwlockRCUperf.eps"
replot
---EOF---
convert rwlockRCUperf.pbm rwlockRCUperf.jpg
