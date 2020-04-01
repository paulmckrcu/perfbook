#!/bin/sh
#
# matmul.reduce.sh: reduce data from matmul.sh output.
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
# Copyright (c) 2010-2019 Paul E. McKenney, IBM.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

sort -k3n -k6n |
tr -d ',' |
awk '	{
	if ($3 != olddim || $6 != nthread) {
		if (olddim != "") {
			print nthread, compdur / fulldur / nthread, minfrac, maxfrac
			if ($3 != olddim)
				print ""
		}
		if ($3 != olddim)
			print "# ", $3
		olddim = $3;
		nthread = $6;
		fulldur = $9;
		compdur = $11;
		maxfrac = $11 / $9 / nthread;
		minfrac = $11 / $9 / nthread;
		n = 1;
	} else {
		fulldur += $9;
		compdur += $11;
		frac = $11 / $9 / nthread;
		if (frac > maxfrac)
			maxfrac = frac;
		if (frac < minfrac)
			minfrac = frac;
		n++;
	}
	}

END	{
	print nthread, compdur / fulldur / nthread, minfrac, maxfrac
	}'
