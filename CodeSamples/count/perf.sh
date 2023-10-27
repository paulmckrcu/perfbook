#!/bin/bash
#
# Runs read-only and update-only performance tests.
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
# Copyright (C) IBM Corporation, 2008-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

nsamples=30

csdir="`pwd | sed -e 's,CodeSamples.*$,CodeSamples,'`"
. $csdir/functions.bash

for ((i = 0; i < $nsamples; i++))
do
	ncpu=1
	while test $ncpu -le $((lastcpu - 2))
	do
		for count in count_atomic count_end count_end_rcu count_lim count_lim_app count_lim_atomic count_lim_sig count_limd count_nonatomic count_stat count_stat_atomic count_stat_eventual
		do
			echo $count $ncpu rperf
			./$count $ncpu rperf
			sleep 0.1
			echo $count $ncpu uperf
			./$count $ncpu uperf
			sleep 0.1
		done
		incr=`power2inc $ncpu $cpusperpwr2`
		ncpu=$((ncpu + incr))
	done
done
