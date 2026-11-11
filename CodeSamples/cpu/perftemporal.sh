#!/bin/bash
#
# Collect temporal data using coe.sh, fre.sh, rfe.sh, and
# "./temporal --coe --nthreads".
#
# Usage: bash perftemporal.sh tag [ [ reps ] nthreads ]
#
# The "tag" parameter is pathname (relative or absolute) at which to
# place the data.  If a date stamp is not already present, a date/time stamp
# will be added to this name of the form "2024.01.17-13.19.34".  The "reps"
# parameter gives the number of data points to collect (default 10) and the
# "nthreads" parameter gives the number of CPUs to use (default one less
# than the number available).
#
# Also run repeated coe.sh and coereduce.sh to get a good multi-value
# plot, and also to get a temporal-diameter estimate for triplot.sh.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright (C) Meta Platforms Inc., 2023
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

if test -z "$1"
then
	echo $0: Need tag path to place data, giving up.
	exit 1
fi
if echo $1 | grep -q '[0-9][0-9][0-9][0-9]\.[0-9][0-9]\.[0-9][0-9]'
	tag="$1"
else
	tag="$1.`date '+%Y.%m.%d-%H.%M.%S'`"
fi
if ! mkdir -p $tag
then
	echo $0: Cannot create $tag, giving up.
	exit 2
fi

T="`mktemp -d ${TMPDIR-/tmp}/perftemporal.sh.XXXXXX`"
trap 'rm -rf $T' 0 2

reps=${2-10}
if test -n "$2"
then
	nthreads=$3
fi
if test -z "$nthreads"
then
	nthreads="`lscpu | grep '^CPU(s):' | awk '{ print $2}'`"
	nthreads="$((nthreads-1))"
fi
if test "$nthreads" -le 2
then
	echo $0: Need more CPUs to produce meaningful data, giving up.
	exit 3
fi

echo $0: $reps repetitions on $nthreads CPUs
echo "  " Output to $tag

# Setup and calibration.
lscpu > $tag/lscpu.out
./tscalibrate > $tag/tscalibrate.out

# Gather coe/fre/rfe histograms.
for pgm in coe fre rfe
do
	# Allow for coe getting only one data point per run,
	# compared to fre and rfe getting $nthreads per run.
	if test "$pgm" = coe
	then
		nr="$((reps*nthreads))"
	else
		nr="$reps"
	fi
	echo $pgm nr: $nr
	for ((i=0;i<nr;i++))
	do
		sh $pgm.sh $nthreads
	done > $tag/$pgm.out
	sort -k4n < $tag/$pgm.out | sh temporalhist.sh > $tag/$pgm.dat
done

# Collect a number-of-values plot and data with which to estimate the
# temporal diameter of system.
for ((i = 1; i <= 100; i++))
do
	./temporal --coe --nthreads $nthreads > $T/coe-nvals.out.$i
	bash coereduce.sh < $T/coe-nvals.out.$i > $T/coe-nvals.dat.$i
done

# Find the best data for the number-of-values plot and extract data
# points for the estimate of the temporal diameter of the system.
maxnvals=0
touch "${tag}/temporal-diameter.dat"
for ((i = 1; i <= 100; i++))
do
	cnv="`awk '{ cnv = $NF } END { print cnv }' < $T/coe-nvals.dat.$i`"
	if test "${cnv}" -gt "${maxnvals}"
	then
		maxnvals="${cnv}"
		maxnvalsidx=$i
	fi
	td="`tail -n 4 $T/coe-nvals.dat.$i | head -1 | awk '{ print $1; }'`"
	echo ${td} >> "${tag}/temporal-diameter.dat"
done

# Copy out the best data for the number-of-values plot.
cp "$T/coe-nvals.out.${maxnvalsidx}" "${tag}/coe-nvals.out"
cp "$T/coe-nvals.dat.${maxnvalsidx}" "${tag}/coe-nvals.dat"

# Reduce the data for the temporal diameter: (1) Sort ascending,
# (2) Compute the fractional increase for each data point,
# (3) Start at the 10th percentile and increase until the
# percent increase exceeds 5%, and take the previous data point.
sort -k1n "${tag}/temporal-diameter.dat" > "${tag}/temporal-diameter.dat.sort"
awk < "${tag}/temporal-diameter.dat.sort" > "${tag}/temporal-diameter.dat.reduce" '{ print $1, ($1 - last) / $1, last; last = $1; }'
awk < "${tag}/temporal-diameter.dat.reduce" > "${tag}/temporal-diameter.est" 'NR < 10 { next; } { if ($2 > 0.05 && cutoff == "") cutoff = $3; } END { print cutoff; }'

exit 0
