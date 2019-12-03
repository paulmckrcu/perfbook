#!/bin/bash
#
# Reduce rotate-only performance varying-size data.
#
# Usage: sh reduceN.sh tag < output-file
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
# Copyright (C) IBM Corporation, 2016-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

tag="$1"

T=/tmp/reduce.sh.$$
trap 'rm -rf $T' 0
mkdir $T

grep -v '^nohup:' | grep -v 'rcu_exit_sig:' > $T/filt
awk -v tag="$tag" < $T/filt '
function output_run(  i, n, maxn) {
	n = 0;
	maxn = 0;
	for (i in sum) {
		if (i + 0 > maxn + 0)
			maxn = i;
	}
	print "#" > old "." tag ".dat";
	for (i = 1; i + 0 <= maxn + 0; i++) {
		if (sum[i] != "") {
			print i, sum[i] / nrec[i] / 1000000, min[i] / 1000000, max[i] / 1000000 >> old "." tag ".dat";
		}
	}
	delete sum;
	delete nrec;
	delete max;
	delete min;
}

/^duration/ {
		rotsize = $9;
		rate = $5 * rotsize / $3;
		sum[rotsize] += rate;
		nrec[rotsize]++;
		if (max[rotsize] == "" || max[rotsize] < rate)
			max[rotsize] = rate;
		if (min[rotsize] == "" || min[rotsize] > rate)
			min[rotsize] = rate;
	}

/^\.\/existence/ && $1 != old && old != "" {
		output_run();
		old = $1;
		nupdaters = $3;
		next;
	}

/^\.\/existence/ {
		old = $1;
		nupdaters = $3;
	}

END	{
		if (old != "")
			output_run();
	}'

# echo "Hit ^C to continue:"
# sleep 10000
