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
# Copyright (C) IBM Corporation, 2016
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

for i in 1 2 3 4 5 6 7 8 9 10
do
	for routetype in route_hazptr route_rcu route_refcnt route_seq route_seqlock
	do
		for ncpu in 1 2 3 4 5 6 7 8
		do
			echo $routetype --perftest --nreaders $ncpu --duration 100 --nelems 10
			./$routetype --perftest --nreaders $ncpu --duration 100 --nelems 10
			sleep 0.1
		done
	done
done
