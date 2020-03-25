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

incr=1
for ((ncpus = 1; ncpus <= lastcpu; ncpus += incr))
do
	for ((i = 0; i < 6; i++))
	do
		for hold in 1 10 100 1000
		do
			./rwlockscale $ncpus $hold 0
		done
	done
	if ((ncpus >= 128))
	then
		incr=4
	elif ((ncpus >= 16))
	then
		incr=2
	fi
done
