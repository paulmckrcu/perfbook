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

for rcu in rcu rcu64 rcu_lock rcu_lock_percpu rcu_nest rcu_nest32 \
	rcu_nest_qs rcu_qs rcu_rcg rcu_rcpg rcu_rcpl rcu_rcpls rcu_ts
do
	for ncpu in 1 2 3 4 6 8
	do
		echo $rcu $ncpu rperf 2
		./$rcu $ncpu rperf 2
		sleep 1
	done
	for ncpu in 1 2 3 4 6 8
	do
		echo $rcu $ncpu uperf 2
		./$rcu $ncpu uperf 2
		sleep 1
	done
done
