#!/bin/bash
#
# Runs single-object-set rotation through three hash tables.
#	And through three skiplists.
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

for pgm in existence_3hash_uperf existence_3skiplist_uperf
do
	for ((i=1;i<=nsamples;i++))
	do
		for ncpu in 1 2 3 4 5 6 7
		do
			echo ./$pgm --nupdaters $ncpu --duration 1000 --updatespacing 20
			./$pgm --nupdaters $ncpu --duration 1000 --updatespacing 20
			sleep 1

		done
	done
done
