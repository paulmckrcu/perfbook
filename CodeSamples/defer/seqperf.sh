#!/bin/bash
#
# Runs performance tests for seqlock.
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
# Copyright (C) IBM Corporation, 2010-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

for ncpu in 1 2 3 4 6 8
do
	echo ./seqlocktorture $ncpu 0 2
	./seqlocktorture $ncpu 0 2
	sleep 0.1
done
for ncpu in 1 2 3 4 6 8
do
	echo ./seqlocktorture $ncpu 1 2
	./seqlocktorture $ncpu 1 2
	sleep 0.1
done
for nelems in 1 2 3 4 6 8 11 16 22 32 44 64 88 128 176 256
do
	echo ./seqlocktorture 8 0 $nelems
	./seqlocktorture 8 0 $nelems
	sleep 0.1
done
