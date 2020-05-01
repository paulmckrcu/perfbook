#!/bin/bash
#
# Categorize averaged CPU-to-CPU response times.
#
# Usage: bash categorize.sh [ cutoff ] < whatever.dat
#
#	"cutoff" is the fraction increase that justifies a new category.
#	So if you want to break on a 30% increase, use 30.
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

cutoff=${1-10}

sort -k2n | gawk -v cutoff=$cutoff '

function docategory (  std)
{
	catavg[curcat] = curavg;
	if (catn[curcat] == 1)
		std = 0;
	else
		std = sqrt(catsumsq[curcat] / catn[curcat] - curavg ^ 2)
	catstd[curcat] = std;
	# print "Change: n: " catn[curcat], "avg: " curavg, "std: " std;
}

BEGIN {
	curcat = -1;
}

{
	cpu = $1;
	curval = $2;
	# print "cpu: " cpu, "curval: " curval;
	if (curcat == -1 || (curval - curavg) / curavg > cutoff / 100) {
		if (curcat != -1)
			docategory()
		curcat++;
	}
	cpuchar = sprintf("%05d", cpu);
	curcatchar = sprintf("%02d", curcat);
	catcpu[curcatchar ":" cpuchar] = curval;
	catn[curcat]++;
	catsum[curcat] += curval;
	catsumsq[curcat] += curval * curval;
	curavg = catsum[curcat] / catn[curcat];
	# print "catcpu[" curcat ":" cpu "]: " catcpu[curcatchar ":" cpuchar], "catn[]: " catn[curcat], "catsum[]: " catsum[curcat], "avg: " curavg;
}

END {
	if (catn[curcat] > 0)
		docategory()
	# print "";
	n = asorti(catcpu, catcpusorted);
	lastcat = 0;
	cpustring = "";
	for (i = 1; i <= length(catcpusorted); i++) {
		split(catcpusorted[i], catpluscpu, ":");
		curcat = catpluscpu[1] + 0;
		curcpu = catpluscpu[2] + 0;
		if (curcat != lastcat) {
			cpustrings[lastcat] = cpustring;
			cpustring = "";
		}
		cpustring = cpustring " " curcpu;
		# print curcat, curcpu, cpustring;
		lastcat = curcat;
	}
	# print "";
	cpustrings[lastcat] = cpustring;
	for (i = 0; i <= curcat; i++)
		print i, catn[i], catavg[i], catstd[i], "CPUs:" cpustrings[i];
}'

exit 0
