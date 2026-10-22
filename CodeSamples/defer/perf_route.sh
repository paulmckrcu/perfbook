#!/bin/bash
#
# Runs read-only performance tests.
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
# Copyright (C) IBM Corporation, 2016-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

csdir="`pwd | sed -e 's,CodeSamples.*$,CodeSamples,'`"
. $csdir/functions.bash

maxtestcpu=$((lastcpu - 1)) # Leave two housekeeping CPUs
cpusperpwr2=4 # Coarser sampling than the default.
for ((i = 1; i <= 30; i++))
do
	for routetype in route_hazptr route_rcu route_rcu_qsbr route_refcnt route_seq route_seqlock
	do
		ncpu=1
		while test $ncpu -le ${maxtestcpu}
		do
			echo $routetype --perftest --nreaders $ncpu --duration 100 --nelems 10
			./$routetype --perftest --nreaders $ncpu --duration 100 --nelems 10
			sleep 0.1
			incr=`power2inc $ncpu $cpusperpwr2 $maxtestcpu`
			ncpu=$((ncpu + incr))
		done
	done
done
