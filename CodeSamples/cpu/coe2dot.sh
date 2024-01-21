#!/bin/bash
#
# Produce digraph from temporal coe data that has been previously
# collected, for example, using: "./temporal --coe --nthreads 15"
#
# Usage: bash coe2dot.sh
#
# Takes the temporal coe data as standard input and produces on standard
# output a graphviz .dot file that shows the partial ordering of stores.
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

grep '^[0-9][0-9]* ' | awk '
BEGIN {
	lastthread = -1;
}

{
	if ($1 != lastthread) {
		lastthread = $1;
	} else {
		print "\t" lastval " -> " $3;
	}
	lastval = $3;
}' | sort -u |
awk '
BEGIN {
	print "digraph PartialOrder {";
	print "\trankdir=\"LR\";";
	lastthread = -1;
}

{
	print $0;
}

END {
	print "}";
}' | tred
