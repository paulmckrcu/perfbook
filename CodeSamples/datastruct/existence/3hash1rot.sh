#!/bin/bash
#
# Runs single-object-set rotation through three hash tables.
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
# Copyright (C) IBM Corporation, 2016
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

nsamples=7

# Simple hash tables, read-only.
for ((i=1;i<=nsamples;i++))
do
	for ncpu in 1 2 3 4 5 6 7
	do
		echo ./existence_3hash_uperf --nupdaters $ncpu --duration 1000 --updatespacing 20
		./existence_3hash_uperf --nupdaters $ncpu --duration 1000 --updatespacing 20
		sleep 1

	done
done
