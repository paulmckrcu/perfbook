#!/bin/bash
#
# Run cachetorture stats, CPU 0 vs. all other CPUs.  First parameter
# controls the maximum CPU number, defaulting to the largest-numbered CPU.
#
# Usage: cachetorture.sh [ testcpu [ lastcpu ] ]
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
# Copyright (C) Facebook, 2020
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

testcpu=${1-0}
maxcpu="`grep '^processor' /proc/cpuinfo | tail -1 | awk '{ print $3 }'`"
lastcpu=${2-$maxcpu}

for ((i=1;i<30;i++))
do
	for ((cpu=0;cpu<=$lastcpu;cpu++))
	do
		if (($cpu==$testcpu))
		then
			continue;
		fi
		for runtype in atomicinc blindcmpxchg cmpxchg write
		do
			./cachetorture $runtype $testcpu $cpu
		done
	done
	./cachetorture locallock
	./cachetorture localcmpxchg
done
