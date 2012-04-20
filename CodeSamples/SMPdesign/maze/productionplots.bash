#!/bin/bash
#
# Create production plots for HOTPAR paper.  Maybe others later.
#
# Usage: productionplots.bash resdir resdir-t paperdir
#	(Or whereever the plots are to be placed.)
#
# This script assumes that reducemazecmp.bash has been run on resdir
# and that reducemazethread.bash has been run on resdir-t.

res=$1
res_t=$2
paperwd=$3

# Produce plots
fontsize=10
plotsize=0.5

f=$res/500
ft=$res_t/1000

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set nokey

# Figure 13: Mean Speedup vs. Number of Threads
set xlabel "Number of Threads"
set ylabel "Mean Speedup Relative to COPART (-O3)"
set label 1 "PWQ" at 6.55,0.33 left
set label 2 "PART" at 1.5,1.2 left
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/1000-ms_2seqO3VfgO3_partO3-mean.eps"
plot "$ft/ms_2seq_O3Vfg_O3.meanq" w l, "$ft/ms_2seq_O3Vpart_O3.meanq" w l, "$ft/ms_2seq_O3Vfg_O3.meanq" w e, "$ft/ms_2seq_O3Vpart_O3.meanq" w e
unset label 1
unset label 2

# Figure 12: Varying Maze Size vs. COPART
set xlabel "Maze Size"
set ylabel "Speedup Relative to SEQ (-O3)"
set logscale x
set label 1 "PWQ" at 230,1.5 left
set label 2 "PART" at 40,1.7 right
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/500-ms_seqO3VfgO3_partO3-median.eps"
plot "$res/ms_seq_O3Vfg_O3.quant" w l, "$res/ms_seq_O3Vpart_O3.quant" w l, "$res/ms_seq_O3Vfg_O3.quant" w e, "$res/ms_seq_O3Vpart_O3.quant" w e

# Figure 11: Varying Maze Size vs. SEQ
set xlabel "Maze Size"
set ylabel "Speedup Relative to COPART (-O3)"
set logscale x
set label 1 "PWQ" at 230,0.46 left
set label 2 "PART" at 43,0.8 right
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/500-ms_2seqO3VfgO3_partO3-median.eps"
plot "$res/ms_2seq_O3Vfg_O3.quant" w l, "$res/ms_2seq_O3Vpart_O3.quant" w l, "$res/ms_2seq_O3Vfg_O3.quant" w e, "$res/ms_2seq_O3Vpart_O3.quant" w e

# Figure 10: Partitioned Coroutines
set xlabel "CDF of Speedup Relative to SEQ (-O3)"
set ylabel "Probability"
set logscale x
set label 1 "PWQ" at 0.95,0.85 right
set label 2 "PART" at 7,0.8 left
set label 3 "COPART" at 6,0.95 right
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/500-ms_seqO3V2seqO3_fgO3_partO3-cdf.eps"
plot "$f/ms_seq_O3V2seq_O3.cdf" w l, "$f/ms_seq_O3Vfg_O3.cdf" w l, "$f/ms_seq_O3Vpart_O3.cdf" w l

# Figure 9: Effect of Compiler Optimization (-O3)
set xlabel "CDF of Speedup Relative to SEQ"
set ylabel "Probability"
set logscale x
set label 1 "PWQ" at 1.5,0.5 right
set label 2 "PART" at 9,0.85 left
set label 3 "SEQ -O3" at 3.5,0.1 left
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/500-ms_seqVfg_part_seqO3-cdf.eps"
plot "$f/ms_seqVfg.cdf" w l, "$f/ms_seqVpart.cdf" w l, "$f/ms_seqVseq_O3.cdf" w l

# Figure 8: Correlation Between Visit Percentage and Solution Time for PART
set xlabel "Percent of Maze Cells Visited"
set ylabel "Solution Time (ms)"
unset logscale x
set label 1 "SEQ" at 70,95 right
set label 2 "PART" at 53,23 left
set label 3 "PWQ" at 75,62 right
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/500-pctVms_seq_part-sct.eps"
plot "$f/pctVms_seq.sct" with dots lw 2, "$f/pctVms_part.sct" with dots lw 2, "$f/pctVms_fg.sct" with dots lw 2

# Figure 7: Reason for Small Visit Percentages (from xfig)

# Figure 6: CDF of SEQ/PWQ and SEQ/PART Solution-Time Ratios
set xlabel "CDF of Speedup Relative to SEQ"
set ylabel "Probability"
set logscale x
set label 1 "SEQ/PWQ" at 1.4,0.5 right
set label 2 "SEQ/PART" at 5,0.5 left
unset label 3
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/500-ms_seqVfg_part-cdf.eps"
plot "$f/ms_seqVfg.cdf" w l, "$f/ms_seqVpart.cdf" w l

# Figure 5: CDF of Solution Times For SEQ, PWQ, and PART
set xlabel "CDF of Solution Time (ms)"
set ylabel "Probability"
unset logscale x
set label 1 "SEQ" at 83,0.5 left
set label 2 "PWQ" at 60,0.7 left
set label 3 "PART" at 30,0.8 left
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/500-ms_seq_fg_part-cdf.eps"
plot "$f/ms_seq.cdf" w l, "$f/ms_fg.cdf" w l, "$f/ms_part.cdf" w l

# Figure 4: Partitioned Parallel Solver Pseudocode

# Figure 3: CDF of Solution Times For SEQ and PWQ
set xlabel "CDF of Solution Time (ms)"
set ylabel "Probability"
unset logscale x
set label 1 "SEQ" at 83,0.5 left
set label 2 "PWQ" at 60,0.7 left
unset label 3
set output "|/home/paulmck/bin/gnuplotepsfix > $paperwd/500-ms_seq_fg-cdf.eps"
plot "$f/ms_seq.cdf" w l, "$f/ms_fg.cdf" w l

# Figure 2: Cell-Number Solution Tracking (xfig)

# Figure 1: SEQ Pseudocode
---EOF---
