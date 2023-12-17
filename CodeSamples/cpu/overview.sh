#!/bin/bash
#
# Gather and plot an overview of cache behavior from the viewpoint
# of CPU 0.
#
# Usage: bash reduce.sh [ destdir [ tag ] ]
#
#	The "destdir" is the destination directory, defaulting to "data"
#	in the temporary directory, which will be created if it does not
#	already exist.	The "tag" identifies the data, and defaults to
#	the basename of "destdir".  The tag given to reduce.sh will be
#	of the form "tag.yyyy.mm.dda", unless "tag" contains a period
#	character, in which case it will be used verbatim.
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

tmpdir=${TMPDIR-/tmp}
destdir="${1-$tmpdir/data}"
defaulttag="`basename $destdir`"
tagstem="${2-$defaulttag}"
if echo ${tagstem} | grep -q '\.' > /dev/null 2>&1
then
	tag="${tagstem}"
else
	tag="${tagstem}.`date +%Y.%m.%da`"
fi

mkdir -p "${destdir}"

lscpu > ${destdir}/lscpu.out
cat /proc/cpuinfo > ${destdir}/cpuinfo.out

echo Starting cachetorture.sh at `date`
bash cachetorture.sh > ${destdir}/cachetorture.sh.out
echo Finished cachetorture.sh at `date`

wd="`pwd`"
cd "${destdir}"
bash "${wd}"/reduce.sh "${tag}" < cachetorture.sh.out
fmt << ---EOF---
Rough plot, for publication quality, copy the gnuplot command from
${wd}/plots.sh to ${destdir} and edit as needed.  Please feel free to
refer to other perfbook plots.sh files for guidance.
---EOF---
bash "${wd}"/plots.sh
