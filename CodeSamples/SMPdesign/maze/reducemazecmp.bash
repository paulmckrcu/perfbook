#!/bin/bash
#
# Reduce data and produce plots.  Start in the maze source directory.
# The first argument is the path to the top-level results directory,
# the one containing the per-maze-size directories.
#
# Usage: bash reducemazecmp.sh dir

. reduce.bash

cd $1

# Create ratio files, but not all possible ratios
for i in `ls | grep '^[0-9]*$'`
do
	# "fg looks good, part looks better, hey, look at -O3!"
	ratio $i/ms_seq $i/ms_fg $i/ms_seqVfg
	ratio $i/ms_seq $i/ms_part $i/ms_seqVpart
	ratio $i/ms_fg $i/ms_part $i/ms_fgVpart
	ratio $i/ms_seq $i/ms_seq_O3 $i/ms_seqVseqO3
	# "See threaded results for additional part scalability"

	# "fg not so good at -O3, part still good -- but coroutines!!!"
	ratio $i/ms_seq_O3 $i/ms_fg_O3 $i/ms_seq_O3Vfg_O3
	ratio $i/ms_seq_O3 $i/ms_part_O3 $i/ms_seq_O3Vpart_O3
	ratio $i/ms_seq_O3 $i/ms_2seq_O3 $i/ms_seq_O3V2seq_O3

	# "OK, compare sequentialized part (2seq) to everything"
	ratio $i/ms_2seq_O3 $i/ms_fg_O3 $i/ms_2seq_O3Vfg_O3
	ratio $i/ms_2seq_O3 $i/ms_part_O3 $i/ms_2seq_O3Vpart_O3

	# "Effects of alignment/padding?"
	ratio $i/ms_seq_O3 $i/ms_seqP_O3 $i/ms_seq_O3VseqP_O3
	ratio $i/ms_2seq_O3 $i/ms_2seqP_O3 $i/ms_2seq_O3V2seqP_O3
	ratio $i/ms_fg_O3 $i/ms_fgP_O3 $i/ms_fg_O3VfgP_O3
	ratio $i/ms_part_O3 $i/ms_partP_O3 $i/ms_part_O3VpartP_O3

	# "Effects of row-first vs. column-first?"
	ratio $i/ms_seq_O3 $i/ms_seqC_O3 $i/ms_seq_O3VseqC_O3
	ratio $i/ms_2seq_O3 $i/ms_2seqC_O3 $i/ms_2seq_O3V2seqC_O3
	ratio $i/ms_fg_O3 $i/ms_fgC_O3 $i/ms_fg_O3VfgC_O3
	ratio $i/ms_part_O3 $i/ms_partC_O3 $i/ms_part_O3VpartC_O3
done

# Create per-file statistics
makecdf_file
quantile_error_file 0.1
average_file

# Create scatter-plot input files
scatter_file

# Produce plots
fontsize=10
plotsize=0.5

wd=`pwd`

for i in `ls | grep '^[0-9]*$'`
do
	cd $wd/$i
	gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set xlabel "CDF of Solution Time (ms)"
set ylabel "Probability"
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seq_fg-cdf.eps"
plot "ms_seq.cdf" w l, "ms_fg.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seq_fg_part-cdf.eps"
plot "ms_seq.cdf" w l, "ms_fg.cdf" w l, "ms_part.cdf" w l
# set output "|/home/paulmck/bin/gnuplotepsfix > ms_seq_fg_part_seqO3-cdf.eps"
# plot "ms_seq.cdf" w l, "ms_fg.cdf" w l, "ms_part.cdf" w l, "ms_seq_O3.cdf" w l
# set output "|/home/paulmck/bin/gnuplotepsfix > ms_seqO3_fgO3_partO3-cdf.eps"
# plot "ms_seq_O3.cdf" w l, "ms_fg_O3.cdf" w l, "ms_part_O3.cdf" w l

set xlabel "CDF of Ratio of Solution Times"
set logscale x
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seqVfg_part-cdf.eps"
plot "ms_seqVfg.cdf" w l, "ms_seqVpart.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > ms_fgVpart-cdf.eps"
plot "ms_fgVpart.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seqVfg_part_seqO3-cdf.eps"
plot "ms_seqVfg.cdf" w l, "ms_seqVpart.cdf" w l, "ms_seqVseq_O3.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seqO3VfgO3_partO3-cdf.eps"
plot "ms_seq_O3Vfg_O3.cdf" w l, "ms_seq_O3Vpart_O3.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seqO3V2seqO3_partO3-cdf.eps"
plot "ms_seq_O3V2seq_O3.cdf" w l, "ms_seq_O3Vpart_O3.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seqO3V2seqO3_fgO3_partO3-cdf.eps"
plot "ms_seq_O3V2seq_O3.cdf" w l, "ms_seq_O3Vfg_O3.cdf" w l, "ms_seq_O3Vpart_O3.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > ms_2seqO3VfgO3_partO3-cdf.eps"
plot "ms_2seq_O3Vfg_O3.cdf" w l, "ms_2seq_O3Vpart_O3.cdf" w l

set xlabel "CDF of Ratio of Cells Visited"
set output "|/home/paulmck/bin/gnuplotepsfix > pct_seqO3VfgO3_partO3-cdf.eps"
plot "pct_seq_O3Vfg_O3.cdf" w l, "pct_seq_O3Vpart_O3.cdf" w l
unset logscale x

set xlabel "Percent of Maze Cells Visited"
set ylabel "Solution Time (ms)"
set output "|/home/paulmck/bin/gnuplotepsfix > pctVms_seq-sct.eps"
plot "pctVms_seq.sct"
set xlabel "Percent of Maze Cells Visited"
set ylabel "Solution Time (ms)"
set output "|/home/paulmck/bin/gnuplotepsfix > pctVms_fg-sct.eps"
plot "pctVms_fg.sct"
set xlabel "Percent of Maze Cells Visited"
set ylabel "Solution Time (ms)"
set output "|/home/paulmck/bin/gnuplotepsfix > pctVms_part-sct.eps"
plot "pctVms_part.sct"
set output "|/home/paulmck/bin/gnuplotepsfix > pctVms_all.eps"
plot "pctVms_seq.sct", "pctVms_fg.sct", "pctVms_part.sct"
---EOF---

done

cd $wd
gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set logscale x
set xlabel "Maze Size"
set ylabel "Solution Time Relative to COPART"
set output "|/home/paulmck/bin/gnuplotepsfix > ms_2seqO3VfgO3_partO3-median.eps"
plot "ms_2seq_O3Vfg_O3.quant" w l, "ms_2seq_O3Vpart_O3.quant" w l, "ms_2seq_O3Vfg_O3.quant" w e, "ms_2seq_O3Vpart_O3.quant" w e
set ylabel "Solution Time Relative to SEQ"
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seqO3VfgO3_partO3-median.eps"
plot "ms_seq_O3Vfg_O3.quant" w l, "ms_seq_O3Vpart_O3.quant" w l, "ms_seq_O3Vfg_O3.quant" w e, "ms_seq_O3Vpart_O3.quant" w e
---EOF---
