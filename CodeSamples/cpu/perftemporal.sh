#!/bin/bash
#
# Collect temporal data using coe.sh, fre.sh, rfe.sh, and
# "./temporal --coe --nthreads".
#
# Usage: bash perftemporal.sh tag [ [ reps ] nthreads ]
#
# The "tag" parameter is pathname (relative or absolute) at
# which to place the data.  A date/time stamp will be added
# to this name of the form "2024.01.17-13.19.34".
# The "reps" parameter gives the number of data points to collect
# (default 10) and the "nthreads" parameter gives the number of
# CPUs to use (default one less than the number available).
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
tag="$1.`date '+%Y.%m.%d-%H.%M.%S'`"
if ! mkdir -p $tag
then
	echo $0: Cannot create $tag, giving up.
	exit 2
fi

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

lscpu > $tag/lscpu.out
./tscalibrate > $tag/tscalibrate.out
./temporal --coe --nthreads $nthreads > $tag/coe-nvals.out
bash coereduce.sh < $tag/coe-nvals.out > $tag/coe-nvals.dat
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
exit 0
