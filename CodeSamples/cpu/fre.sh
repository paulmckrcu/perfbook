#!/bin/bash
#
# Produce and reduce temporal fre data.
#
# Usage: bash fre.sh [ nthreads ]
#
# Sample output:
#
# 0 140737508 140737516 8
# 1 140737502 140737516 14
# 2 140737524 140737516 -8!!!
# 3 140737504 140737516 12
# 4 140737520 140737516 -4!!!
# 5 140737504 140737516 12
# 6 140737486 140737516 30
# 7 140737516 140737516 0
# 8 140737492 140737516 24
# 9 140737516 140737516 0
# 10 140737492 140737516 24
# 11 140737496 140737516 20
# 12 140737512 140737516 4
# 13 140737512 140737516 4
# 14 140726084 140737516 11432
#
# The first number is the thread ID, the second number the start time
# of the read that observed the value change, the third number is the
# end time of the store, the fourth number is the time difference
# followed by exclamation marks if this number is negative.  All times
# are in nanoseconds since a time near the start of the run.
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

./temporal --fre --nthreads ${1-15} |
awk '
/^Write/ {
	et = $4;
	for (i in st) {
		print i, st[i], et, et - st[i] (et < st[i] ? "!!!" : "");
	}
}

$1 ~ /^[0-9][0-9]*$/ && $3 == 0 {
	st[$1] = $5;
}'
