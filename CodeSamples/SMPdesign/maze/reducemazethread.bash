#!/bin/bash
#
# Reduce data and produce plots for threaded runs.  Start in the maze
# source directory.  The first argument is the path to the top-level
# results directory, the one containing the per-maze-size directories.
#
# Usage: bash reducemazethread.sh dir

. reduce.bash

cd $1

# Create ratio files, but not all possible ratios
for i in `ls | grep '^[0-9]*$' | sort -k1n`
do
	touch $i/ms_2seq_O3Vfg_O3.quant
	touch $i/ms_2seq_O3Vfg_O3.mean
	touch $i/ms_2seq_O3Vfg_O3.meanq
	touch $i/ms_2seq_O3Vpart_O3.quant
	touch $i/ms_2seq_O3Vpart_O3.mean
	touch $i/ms_2seq_O3Vpart_O3.meanq
	for j in `cd $i; ls ms_fg_O3-* | grep -v '\.' | sed -e 's/ms_fg_O3-//' | sort -k1n`
	do
		ratio $i/ms_2seq_O3 $i/ms_fg_O3-$j $i/ms_2seq_O3Vfg_O3-$j
		echo $j `quantile_error 0.1 $i/ms_2seq_O3Vfg_O3-$j` >> $i/ms_2seq_O3Vfg_O3.quant
		echo $j `average $i/ms_2seq_O3Vfg_O3-$j` >> $i/ms_2seq_O3Vfg_O3.mean
		echo $j `average $i/ms_2seq_O3Vfg_O3-$j` \
			`quantile_error 0.1 $i/ms_2seq_O3Vfg_O3-$j | \
			awk '{ print $2, $3 }'` >> $i/ms_2seq_O3Vfg_O3.meanq
		ratio $i/ms_2seq_O3 $i/ms_part_O3-$j $i/ms_2seq_O3Vpart_O3-$j
		echo $j `quantile_error 0.1 $i/ms_2seq_O3Vpart_O3-$j` >> $i/ms_2seq_O3Vpart_O3.quant
		echo $j `average $i/ms_2seq_O3Vpart_O3-$j` >> $i/ms_2seq_O3Vpart_O3.mean
		echo $j `average $i/ms_2seq_O3Vpart_O3-$j` \
			`quantile_error 0.1 $i/ms_2seq_O3Vpart_O3-$j | \
			awk '{ print $2, $3 }'` >> $i/ms_2seq_O3Vpart_O3.meanq
	done
done

# Create per-file statistics
makecdf_file

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
set xlabel "Number of Threads"
set ylabel "Median Solution Time Relative to COPART"
set output "|/home/paulmck/bin/gnuplotepsfix > ms_2seqO3VfgO3_partO3-quant.eps"
plot "ms_2seq_O3Vfg_O3.quant" w l, "ms_2seq_O3Vpart_O3.quant" w l
set ylabel "Mean Solution Time Relative to COPART"
set output "|/home/paulmck/bin/gnuplotepsfix > ms_2seqO3VfgO3_partO3-mean.eps"
plot "ms_2seq_O3Vfg_O3.mean" w l, "ms_2seq_O3Vpart_O3.mean" w l
set output "|/home/paulmck/bin/gnuplotepsfix > ms_2seqO3VfgO3_partO3-meanq.eps"
plot "ms_2seq_O3Vfg_O3.meanq" w l, "ms_2seq_O3Vpart_O3.meanq" w l, "ms_2seq_O3Vfg_O3.meanq" w e, "ms_2seq_O3Vpart_O3.meanq" w e
---EOF---

done
