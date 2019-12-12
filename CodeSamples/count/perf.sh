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

for count in count_atomic count_end count_end_rcu count_lim count_lim_app count_lim_atomic count_lim_sig count_limd count_nonatomic count_stat count_stat_atomic count_stat_eventual
do
	for ncpu in 1 2 3 4 5 6 7 8 10 12 14 16 20 24 28 32 40 48 56 64 80 96 112 128 160 192 224 256 320 384 420
	do
		for ((i = 0; i < $nsamples; i++))
		do
			echo $count $ncpu rperf 2
			./$count $ncpu rperf 2
			sleep 1
		done
	done
	for ncpu in 1 2 3 4 5 6 7 8 10 12 14 16 20 24 28 32 40 48 56 64 80 96 112 128 160 192 224 256 320 384 420
	do
		for ((i = 0; i < $nsamples; i++))
		do
			echo $count $ncpu uperf 2
			./$count $ncpu uperf 2
			sleep 1
		done
	done
done
