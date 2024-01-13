#!/bin/bash
#
# Reduce data gathered by fre.sh and rfe.sh as standard input.
# The histogram output (time, count) will be emitted on standard output.
# The is suitable for gnuplot, though stray values due to delays in the
# test may need to be manually trimmed.
#
# Example usage:
#	for ((i=0;i<1000;i++))
#	do
#		sh coe.sh
#	done sort -k4n | sh temporalhist.sh
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
# Copyright (C) Meta Platforms Inc., 2023
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

sed -e 's/!!!//' | grep '^[0-9][0-9]* ' |
awk '
curval != $4 {
	if (curval != "")
		print curval, nvals;
	curval = $4;
	nvals = 0;
}

{
	nvals++;
}

END {
	if (curval != "")
		print curval, nvals;
}'
