#! /bin/sh

fontsize=10
plotsize=0.7

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
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
