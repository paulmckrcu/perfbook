#!/bin/sh

fontsize=12
plotsize=1
przsize="nosquare 1.2,0.375"
font=`kpsewhich uhvr8a.pfb`

gnuplot << ---EOF---
set term postscript portrait color ${fontsize} enhanced "NimbusSanL-Regu" fontfile "${font}"
set colorsequence podo
set size $przsize
set output "RCU-test-ratio.eps"
set xlabel "Linux Release"
set ylabel "LoC"
set y2label "\% Test"
set boxwidth 0.7 relative
unset xtics
set xtics 1,2 nomirror rotate by 90 right scale 0
set ytics 1 5000
set ytics out
set y2tics 1 10
set y2tics out
set ytics nomirror
set yrange [0:35000]
set y2range [0:50]
set style data histogram
set style histogram rowstacked
set style fill solid 0.18 border -1
set key top center
# Set linestyle 1
set style line 1 \
    linetype 1 linewidth 0.5 \
    pointtype 7 pointsize 0.5

# Set linestyle 2
set style line 2 \
    linetype 4 lc 'dark-red' linewidth 1.5 \
    pointtype 8 pointsize 0.5

#plot 'rcu-test.dat' using 0:xtic(1), for [i=2:3] '' using i linestyle 1
plot 'rcu-test.dat' using 2 t "RCU", '' using 3:xticlabels(1) t "RCU Test", \
     '' using 5 with line linestyle 2 axis x1y2 t "\% Test"
---EOF---
