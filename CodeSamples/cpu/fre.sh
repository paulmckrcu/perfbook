#!/bin/bash
#
# Produce and reduce temporal fre data.
#
# Usage: bash fre.sh [ nthreads ]
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
