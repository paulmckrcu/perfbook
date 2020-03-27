#!/bin/bash
#
# Data-reduction script for rwlockscale.
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
# Copyright (C) IBM Corporation, 2009-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

awk '	{
		if ($5 == 0)
			next;
		i = $3 ":" $5;
		n[i]++;
		sum[i] += $9;
		if ($9 > max[i])
			max[i] = $9;
		if ($9 < min[i] || min[i] == "")
			min[i] = $9;
	}

END	{
		for (i in n) {
			split(i, a, ":");
			t = a[1];
			d = a[2];
			avg[i] = sum[i] / n[i];
			if (t == 1) {
				base[d] = avg[i];
				basemin[d] = min[i];
				basemax[d] = max[i];
				print "# #", d, base[d], basemin[d], basemax[d], basemax[d] / basemin[d]
			}
		}
		for (i in n) {
			split(i, a, ":");
			t = a[1];
			d = a[2];
			s = t * base[d];
			smin = t * basemin[d];
			smax = t * basemax[d];
			print d, t, avg[i] / s, min[i] / smax, max[i] / smin;
		}
	}' |
sort -k1n -k2n |
awk '	{
	if (oldd != "" && oldd != $1) {
		print "";
	}
	oldd = $1;
	print $2, $3, $4, $5, $6, $7;
	}'
