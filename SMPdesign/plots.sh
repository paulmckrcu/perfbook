#! /bin/sh

fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term pbm medium
set output "clockfreq.pbm"
set xlabel "Year"
set ylabel "CPU Clock Frequency"
set logscale y
#set yrange [1:10000]
set yrange [100:10000]
set nokey
set xtics rotate
# set label 1 "rcu" at 0.1,10 left
# set label 2 "spinlock" at 0.5,3.0 left
# set label 3 "brlock" at 0.4,0.6 left
# set label 4 "rwlock" at 0.3,1.6 left
# set label 5 "refcnt" at 0.15,2.8 left
#plot "clockfreq.dat", "clockfreqP4.dat", "clockfreqP3.dat"
plot "clockfreqP4.dat", "clockfreqP3.dat", "clockfreqP2.dat", "clockfreqPPro.dat", "clockfreqXeonDC.dat"
# plot "clockfreqP4.dat", "clockfreqP3.dat", "clockfreqP2.dat"
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|../utilities/gnuplotepsfix > clockfreq.eps"
replot
---EOF---
ppmtogif clockfreq.pbm > clockfreq.gif 2> /dev/null

gnuplot << ---EOF---
set term gif
set size square ${plotsize},${plotsize}
set output "synceff.gif"
set xlabel "Number of CPUs/Threads"
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
set term postscript portrait
set output "|../utilities/gnuplotepsfix > synceff.eps"
replot
---EOF---

gnuplot << ---EOF---
set term gif
set size square ${plotsize},${plotsize}
set output "matmuleff.gif"
set xlabel "Number of CPUs/Threads"
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
set term postscript portrait
set output "|../utilities/gnuplotepsfix > matmuleff.eps"
replot
---EOF---
