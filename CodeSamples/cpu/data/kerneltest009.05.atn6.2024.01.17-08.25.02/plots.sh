#!/bin/sh

gnuplot << ---EOF---
set term png
set output "coe-nvals.png"
set xlabel "Time (Timestamp Periods)"
set ylabel "Number of Simultaneous Values"
#set logscale y
set xrange [:10000]
#set yrange [100:10000]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "coe-nvals.dat" w l
---EOF---

gnuplot << ---EOF---
set term png
set output "coe.png"
set xlabel "Store-to-Store Latency (Timestamp Periods)"
set ylabel "Number of Samples"
#set logscale y
set xrange [-1000:3000]
set yrange [0:]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "coe.dat" w points pt 6 pointsize 0.2
---EOF---

gnuplot << ---EOF---
set term png
set output "fre.png"
set xlabel "Store-to-Load Latency (Timestamp Periods)"
set ylabel "Number of Samples"
#set logscale y
set xrange [-250:50]
set yrange [0:]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "fre.dat" w points pt 6 pointsize 0.5
---EOF---

gnuplot << ---EOF---
set term png
set output "rfe.png"
set xlabel "Store-to-Load Latency (Timestamp Periods)"
set ylabel "Number of Samples"
#set logscale y
set xrange [0:350]
set yrange [0:]
set nokey
# set label 1 "RCU" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "rfe.dat" w points pt 6 pointsize 0.5
---EOF---
