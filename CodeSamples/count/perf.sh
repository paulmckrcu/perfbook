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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
#
# Copyright (C) IBM Corporation, 2008
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

nsamples=5

for count in count_atomic count_end count_end_rcu count_lim count_lim_app count_lim_atomic count_lim_sig count_limd count_nonatomic count_stat count_stat_atomic
do
	for ncpu in 1 2 3 4 5 6 7 8
	do
		for ((i = 1; i < $nsamples; i++))
		do
			echo $count $ncpu rperf 2
			./$count $ncpu rperf 2
			sleep 1
		done
	done
	for ncpu in 1 2 3 4 5 6 7 8
	do
		for ((i = 1; i < $nsamples; i++))
		do
			echo $count $ncpu uperf 2
			./$count $ncpu uperf 2
			sleep 1
		done
	done
done
