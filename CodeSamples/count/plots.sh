#! /bin/sh

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > atomic.eps"
set xlabel "Number of CPUs/Threads"
set ylabel "Time Per Increment (nanoseconds)"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "data/count_atomic:u.2009.05.03a.dat" w e, "data/count_atomic:u.2009.05.03a.dat" w l, 8.81772
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > atomic125.eps"
set xlabel "Number of CPUs/Threads"
set ylabel "Time Per Increment (ns)"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "data/count_atomic\:u.2009.05.25a.dat" w e, "data/count_atomic\:u.2009.05.25a.dat" w l, 8.81772
set term png medium
set output "atomic125.png"
replot
---EOF---

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|../../utilities/gnuplotepsfix > atomic_nehalem.eps"
set xlabel "Number of CPUs/Threads"
set ylabel "Time Per Increment (ns)"
#set logscale y
#set yrange [1:10000]
#set yrange [100:10000]
set nokey
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
plot "data/count_atomic:u.elm3b128.2009.05.29a.dat" w e, "data/count_atomic:u.elm3b128.2009.05.29a.dat" w l
set term png medium
set output "atomic_nehalem.png"
replot
---EOF---
