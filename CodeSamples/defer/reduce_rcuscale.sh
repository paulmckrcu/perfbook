#!/bin/bash
#
# Reduce data gathered by rcuscale.sh or rcudelay.sh.
#
# Usage: bash reduce_rcuscale.sh [ tag ] < rcuscale.sh.out
#
#	If present, the "tag" will be included in the output filenames,
#	for example, rcu-eb.<tag>.dat.  The output files are
#	formatted for use as gnuplot data files.
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
# Copyright (C) Facebook, 2020
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

tag="$1"

# Gather data from each primitive <prim> into separate <prim>-points.<tag>.dat
# and <prim>-eb.<tag>.dat, the former for point-cloud plots and the latter
# for line and error-bar plots.
awk -v tag="$tag" '
/^Run for/ {
	prim = $3;
	ncpus = $5;
	if (NF >= 9) {
		delay = $9
		if (nodelay == "y") {
			print "Mixed rcuscale/rcudelay input!" > "/dev/stderr";
			exit 1;
		}
	} else if (delay != "") {
		print "Mixed rcuscale/rcudelay input!" > "/dev/stderr";
		exit 1;
	} else {
		nodelay = "y";
	}
	next;
}

/^Points: / {
	# print "> " prim "-points." tag ".dat"
	for (i = 2; i <= NF; i++) {
		# print ncpus, $i
		if (nodelay == "y")
			print ncpus, $i > prim "-points." tag ".dat"
		else
			print delay, $i > prim "-" ncpus "-points." tag ".dat"
	}
}

/^Minimum reader duration: / {
	minval = $4;
}

/^Median reader duration: / {
	medval = $4;
}

/^Maximum reader duration: / {
	maxval = $4;
	# print "> " prim "-eb." tag ".dat"
	# print ncpus, medval, minval, maxval
	if (nodelay == "y")
		print ncpus, medval, minval, maxval > prim "-eb." tag ".dat"
	else
		print delay, medval, minval, maxval > prim "-" ncpus "-eb." tag ".dat"
}'
