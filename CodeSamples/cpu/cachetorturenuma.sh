#!/bin/bash
#
# Run cachetorture stats in a topology-aware manner.  First parameter
# controls the maximum CPU number, defaulting to the largest-numbered CPU.
# Second parameter gives the number of contiguous CPU numbers associated
# with a socket, defaulting to 28.
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

runtypes="atomicinc blindcmpxchg cmpxchg write"

maxcpu="`grep '^processor' /proc/cpuinfo | tail -1 | awk '{ print $3 }'`"
lastcpu=${1-$maxcpu}
socketrun=${2-28}

echo maxcpu: $maxcpu lastcpu: $lastcpu socketrun: $socketrun

for ((i=1;i<30;i++))
do
	for ((cpu0=0;cpu0<=$lastcpu;cpu0+=$socketrun))
	do
		for ((cpu1=$cpu0+1;cpu1<$cpu0+$socketrun;cpu1++))
		do
			for runtype in $runtypes
			do
				./cachetorture $runtype $cpu0 $cpu1
			done
		done
		for ((cpu1=$cpu0+$socketrun;cpu1<=$lastcpu;cpu1+=$socketrun))
		do
			for runtype in $runtypes
			do
				./cachetorture $runtype $cpu0 $cpu1
			done
		done
	done
done
