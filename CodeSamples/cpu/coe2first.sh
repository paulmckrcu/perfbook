#!/bin/bash
#
# Produce first thread/value reads from temporal coe data that has been
# previously collected, for example, using: "./temporal --coe --nthreads 15"
#
# Usage: bash coe2first.sh
#
# Takes the temporal coe data as standard input and produces on standard
# output a table of numbers in thread order, when that thread first started
# a read and when the first read that returned its value started.
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
# Copyright (C) Meta Platform Inc., 2023
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

grep '^[0-9][0-9]* ' | sort -k2n | awk '
BEGIN {
	timeoffset = "";
}

timeoffset == "" {
	timeoffset = $2 - 25;
}

{
	if (ft[$1] == "") {
		ft[$1] = $2 - timeoffset;
	}
	if (fv[$3] == "") {
		fv[$3] = $2 - timeoffset;
	}
}

END {
	printf "%4s %8s %8s\n", "", "FT", "FV";
	for (i in ft) {
		printf "%4d %8d %8d %s\n", i, ft[i], fv[i], ft[i] != fv[i] ? "<-" : "";
	}
}'
