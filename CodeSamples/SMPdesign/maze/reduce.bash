#!/bin/bash
#
# Data-reduction functions.
#
# Usage: . reduce.bash

# Produce file containing line-by-line ratio of the two specified files.
# The input files must be unsorted.
#
# Usage: ratio path1 path2 path3
ratio()
{
	awk '{ getline l <"'"$1"'"; print l / $1; }' < $2 > $3
}

# Produce gnuplot-ready scatterplot from unsorted input files.
#
# Usage: scatter path1 path2 path3.sct
scatter ()
{
	awk '{ getline l <"'"$1"'"; print l, $1; }' < $2 > $3
}

# Produce gnuplot-ready scatterplots from all pct/ms pairs in all
# subdirectories.
#
# Usage: scatter_file
scatter_file ()
{
	local f
	local i
	local j

	for i in `ls | egrep '^[0-9]*$|^[0-9]*x[0-9]*$'`
	do
		for j in `ls $i/pct_* | egrep '^([0-9]*|[0-9]*x[0-9]*)/[a-zA-Z0-9_-]*$'`
		do
			ms=`echo $j | sed 's/\/pct_/\/ms_/'`
			mstail=`echo $ms | sed 's/^[0-9]*\///'`
			f=$i/pctV$mstail.sct
			scatter $j $ms $f
		done
	done
}

# Produce gnuplot-ready CDF data file from unsorted input file.
#
# Usage: makecdf inputpath
#
# Produces sorted inputpath.sort and a gnuplot-ready inputpath.cdf
makecdf ()
{
	local count

	if test -f $1 -a ! -e $1.sort
	then
		sort -k1n $1 > $1.sort
	fi
	count=`wc -l $1.sort | awk '{ print $1 }'`
	awk '{ print $1, NR / '"$count"' }' < $1.sort > $1.cdf
}

# Given a set of directories whose names are the maze size, produce
# gnuplot files of the CDFs of individual data files.  This must be run
# in the parent directory of the maze-size directories.
#
# Usage: makecdf_file
makecdf_file ()
{
	local f
	local i
	local j

	for i in `ls | egrep '^[0-9]*$|^[0-9]*x[0-9]*$' | sort -k1n`
	do
		for j in `ls $i/ms_* $i/pct_* | egrep '^([0-9]*|[0-9]*x[0-9]*)/[a-zA-Z0-9_-]*$'`
		do
			makecdf $j
		done
	done
}

# Compute the specified quantile given a sorted input file.
# Output the quantile on standard output.
#
# Usage: quantile q inputpath
quantile ()
{
	if test -f $2 -a ! -e $2.sort
	then
		sort -k1n $2 > $2.sort
	fi
	awk '	{
			d[NR - 1] = $1
		}

	END	{
			x = (NR - 1) * '"$1"';
			ix = int(x);
			l = d[ix];
			h = d[ix + 1];
			print l + (x - ix) * (h - l);
		}' < $2.sort
}

# Output quantile error ranges as a single line in gnuplot format.
#
# Usage: quantile_error confidence inputpath
quantile_error ()
{
	local ql
	local qh

	qh=`awk 'BEGIN { print 1 - '"$1"' / 2 }' < /dev/null`
	ql=`awk 'BEGIN { print '"$1"' / 2 }' < /dev/null`
	echo `quantile 0.5 $2` `quantile $ql $2` `quantile $qh $2`
}

# Given a set of directories whose names are the x value, produce
# a quantile gnuplot file suitable for "with errorbars" plots.  This must
# be run in the parent directory of the x-value directories.
#
# Usage: quantile_error_file confidence
quantile_error_file ()
{
	local f
	local i
	local j

	for i in `ls | egrep '^[0-9]*$|^[0-9]*x[0-9]*$' | sort -k1n`
	do
		for j in `ls $i/ms_* $i/pct_* | egrep '^([0-9]*|[0-9]*x[0-9]*)/[a-zA-Z0-9_-]*$'`
		do
			f=`echo $j | sed -e 's/^.*\///'`.quant
			touch $f
			echo $i `quantile_error $1 $j` >> $f
		done
	done
}

# Compute the average given an input file, sorted or not.
# Output the average on standard output.
# 
# Usage: average inputpath
average ()
{
	awk '{ sum += $1 } END { print sum / NR }' < $1
}

# Given a set of directories whose names are the x value, produce
# a gnuplot file of averages.  This must be run in the parent directory
# of the x-value directories.
#
# Usage: average_file
average_file ()
{
	local f
	local i
	local j

	for i in `ls | egrep '^[0-9]*$|^[0-9]*x[0-9]*$' | sort -k1n`
	do
		for j in `ls $i/ms_* $i/pct_* | egrep '^([0-9]*|[0-9]*x[0-9]*)/[a-zA-Z0-9_-]*$'`
		do
			f=`echo $j | sed -e 's/^.*\///'`.mean
			touch $f
			echo $i `average $j` >> $f
		done
	done
}
