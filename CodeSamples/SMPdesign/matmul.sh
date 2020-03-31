#!/bin/bash
#
# matmul.sh: simple script to run the matmul program.
#
# Usage: bash matmul.sh [ lastcpu ]
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
# Copyright (c) 2009-2019 Paul E. McKenney, IBM.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

maxcpu="`grep '^processor' /proc/cpuinfo | tail -1 | awk '{ print $3 }'`"
lastcpu=${1-$maxcpu}

for ((i = 0; i < 30; i++))
do
	incr=1
	for ((ncpus = 1; ncpus <= lastcpu + 1; ncpus += incr))
	do
		for dim in 64 128 256 512 1024
		do
			./matmul $dim $ncpus
		done
		if ((ncpus >= 128))
		then
			incr=32
		elif ((ncpus >= 64))
		then
			incr=16
		elif ((ncpus >= 32))
		then
			incr=8
		elif ((ncpus >= 16))
		then
			incr=4
		elif ((ncpus >= 8))
		then
			incr=2
		fi
	done
done
