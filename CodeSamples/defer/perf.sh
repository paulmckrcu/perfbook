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

for rcu in rcu rcu64 rcu_lock rcu_lock_percpu rcu_nest \
	rcu_nest_qs rcu_qs rcu_rcg rcu_rcpg rcu_rcpl rcu_rcpls rcu_ts
do
	for ncpu in 1 2 3 4 6 8
	do
		echo $rcu $ncpu rperf
		./$rcu $ncpu rperf
	done
	for ncpu in 1 2 3 4 6 8
	do
		echo $rcu $ncpu uperf
		./$rcu $ncpu uperf
	done
done
