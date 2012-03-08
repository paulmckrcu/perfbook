#!/bin/bash
#
# Reduce data and produce plots
#
# Usage: bash plots.sh

# Produce CDFs, but only for filenames not containing "."
for i in `ls ms_* pct_* | grep '^[a-zA-Z0-9_]*$'`
do
	sort -k1n $i > $i.sort
	count=`wc -l $i.sort | awk '{ print $1 }'`
	awk '{ print $1, NR / '"$count"' }' < $i.sort > $i.cdf
done

# Produce scatter plots
awk '{ getline l <"pct_seq_O3"; print l, $1; }' < ms_seq_O3 > pctVms_seq_O3.sct
awk '{ getline l <"pct_fg_O3"; print l, $1; }' < ms_fg_O3 > pctVms_fg_O3.sct
awk '{ getline l <"pct_part_O3"; print l, $1; }' < ms_part_O3 > pctVms_part_O3.sct

# Produce plots
fontsize=10
plotsize=0.5

gnuplot << ---EOF---
set term postscript portrait ${fontsize}
set size square ${plotsize},${plotsize}
set output "|/home/paulmck/bin/gnuplotepsfix > unopt.eps"
set xlabel "CDF of Solution Time (ms)"
set ylabel "Probability"
plot "ms_seq.cdf" w l, "ms_fg.cdf" w l, "ms_part.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > unoptO3.eps"
plot "ms_seq.cdf" w l, "ms_fg.cdf" w l, "ms_part.cdf" w l, "ms_seq_O3.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > optO3.eps"
plot "ms_seq_O3.cdf" w l, "ms_fg_O3.cdf" w l, "ms_part_O3.cdf" w l

set xlabel "CDF of Ratio of Solution Times"
set output "|/home/paulmck/bin/gnuplotepsfix > unoptratO3.eps"
plot "ms_seqVfg.cdf" w l, "ms_seqVpart.cdf" w l, "ms_seqVseq_O3.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > unoptrat.eps"
plot "ms_seqVfg.cdf" w l, "ms_seqVpart.cdf" w l
set output "|/home/paulmck/bin/gnuplotepsfix > optratO3.eps"
plot "ms_seq_O3Vfg_O3.cdf" w l, "ms_seq_O3Vpart_O3.cdf" w l

set xlabel "CDF of Ratio of Cells Visited"
set output "|/home/paulmck/bin/gnuplotepsfix > pctratO3.eps"
plot "pct_seq_O3Vfg_O3.cdf" w l, "pct_seq_O3Vpart_O3.cdf" w l

set xlabel "Percent of Maze Cells Visited"
set ylabel "Solution Time (ms)"
set output "|/home/paulmck/bin/gnuplotepsfix > pctVms_seq_O3.eps"
plot "pctVms_seq_O3.sct"
set xlabel "Percent of Maze Cells Visited"
set ylabel "Solution Time (ms)"
set output "|/home/paulmck/bin/gnuplotepsfix > pctVms_fg_O3.eps"
plot "pctVms_fg_O3.sct"
set xlabel "Percent of Maze Cells Visited"
set ylabel "Solution Time (ms)"
set output "|/home/paulmck/bin/gnuplotepsfix > pctVms_part_O3.eps"
plot "pctVms_part_O3.sct"
set output "|/home/paulmck/bin/gnuplotepsfix > pctVms_all.eps"
plot "pctVms_seq_O3.sct", "pctVms_fg_O3.sct", "pctVms_part_O3.sct"
---EOF---
