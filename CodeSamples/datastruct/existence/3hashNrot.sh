#!/bin/bash
#
# Runs single-object-set rotation through three hash tables, but
# varying number of elements rotated.
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
# Copyright (C) IBM Corporation, 2016-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

nsamples=7

# Simple hash tables, read-only.
for ((i=1;i<=nsamples;i++))
do
	for updsp in 20 23 26 29 32 35 38 41 44 47 50 53 56 59 62 65 68 71 74 77 80 83 86 89 92 95 98 101 104 107 110 113
	do
		echo ./existence_3hash_uperf --nupdaters 7 --duration 1000 --updatespacing $updsp
		./existence_3hash_uperf --nupdaters 7 --duration 1000 --updatespacing $updsp
		sleep 1

	done
done
