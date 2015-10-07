#!/bin/bash
#
# Test script for rwlockscale
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
# Copyright (C) IBM Corporation, 2009
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

for ((ncpus = 1; ncpus <= 128; ncpus += 2))
do
	for hold in 1000 10000 100000 1000000 10000000 100000000
	do
		for ((i = 0; i < 3; i++))
		do
			./prwl_scale $ncpus $hold 0
			./prwl_scale $ncpus 0 $hold
		done
	done
done
