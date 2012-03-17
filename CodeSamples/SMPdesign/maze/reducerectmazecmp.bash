#!/bin/bash
#
# Reduce data and produce plots.  Start in the maze source directory.
# The first argument is the path to the top-level results directory,
# the one containing the per-maze-size directories.
#
# Usage: bash reducerectmazecmp.sh dir

. reduce.bash

cd $1

# Create ratio files, but not all possible ratios
for i in `ls | grep '^[0-9]*x[0-9]*$'`
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

# Convert NxM to ratio
for i in *.quant
do
	sed -e 's/x/ /' < $i | awk '{ print $2/$1, $3, $4,$5 }' > $i.dat
done

# Produce plots
fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set xlabel "Ratio of Short Side to Long Side"
set ylabel "Speedup of PART relative to SEQ"
set logscale x
set nokey
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seqVpart.quant.eps"
plot "ms_seqVpart.quant.dat" w l, "ms_seqVpart.quant.dat" w e
set ylabel "Speedup of PART relative to SEQ (-O3)"
set output "|/home/paulmck/bin/gnuplotepsfix > ms_seq_O3Vpart_O3.quant.eps"
plot "ms_seq_O3Vpart_O3.quant.dat" w l, "ms_seq_O3Vpart_O3.quant.dat" w e
---EOF---
