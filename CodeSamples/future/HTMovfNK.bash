#!/bin/bash
#
# Compute cache-overflow probabilities for cache with specified size,
# line size, and associativity.
#
# Usage:
#
#	HTMovfNK.bash cachesize assoc linesize
#
# Note that "cachesize" is in kilobytes, but "linesize" is in bytes.
#
# Produces gnuplot-consumable output.
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
# Copyright (C) IBM Corporation, 2012-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

cachesize=$1
assoc=$2
linesize=$3
cachelines=$(($cachesize*1024/$linesize))

for ((i=1;i<=$cachelines+1;i++))
do
	sets=$(($cachelines/$assoc))
	p=`./HTMovf p $sets $assoc $i | maxima |
		grep @@@ | sed -e 's/^.*=//' -e 's/b/e/'`
	echo $i $p
done
