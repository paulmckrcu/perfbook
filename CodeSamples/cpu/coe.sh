#!/bin/bash
#
# Produce and reduce temporal coe data.
#
# Usage: bash coe.sh [ nthreads ]
#
# Sample output:
#
# 2 2234900 2235044 -144 !!!
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
# Copyright (C) Meta Platforms Inc., 2024
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

./temporal --coe --nthreads ${1-15} |
awk '
BEGIN {
	lastentry = "";
	maxtime = "";
	winningcpu = -1;
}

/^COE-write / {
	if (lastentry != "") # @@@
		print "Last entry: " lastentry; # @@@
	st[$2] = $3;
	et[$2] = $5;
	# print  "Input line: " $0 # @@@
}

$1 ~ /^[0-9][0-9]*$/ {
	if (maxtime == "" || maxtime < $2) {
		maxtime = $2;
		winningcpu = $3;
		# lastentry = $0; # @@@
	}
}

/^COE-final / {
	winningcpu = $2;
	# print $0
}

END {
	# print "Winning CPU: " winningcpu; # @@@
	mindelta = "";
	for (i in st) {
		if (i == winningcpu)
			continue;
		delta = et[winningcpu] - st[i];
		# print "Delta for CPU " i ": " et[winningcpu] " - " st[i] " = " delta; # @@@
		if (mindelta == "" || mindelta > delta) {
			mindelta = delta;
			min_et = et[winningcpu];
			min_st = st[i];
		}
	}
	print winningcpu, min_et, min_st, mindelta, mindelta < 0 ? "!!!" : "";
}'
