#!/bin/bash
#
# Test script for rwlockscale
#
# Usage: rwlockscale.sh [ lastcpu ]
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
# Copyright (C) IBM Corporation, 2009-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

maxcpu="`grep '^processor' /proc/cpuinfo | tail -1 | awk '{ print $3 }'`"
lastcpu=${1-$maxcpu}

for ((ncpus = 1; ncpus <= lastcpu; ncpus += 2))
do
	for hold in 1000 10000 100000 1000000 10000000 100000000
	do
		for ((i = 0; i < 3; i++))
		do
			./rwlockscale $ncpus $hold 0
			./rwlockscale $ncpus 0 $hold
		done
	done
done
