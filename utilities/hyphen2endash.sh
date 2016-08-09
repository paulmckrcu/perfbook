#!/bin/sh
#
# Find hyphens used for number range and replace them with en dashes.
#
# Replacement candidates are
# Lines~nn-mm -> Lines~nn--mm
# Lines nn-mm -> Lines~nn--mm
# lines~nn-mm -> lines~nn--mm
# lines nn-mm -> lines~nn--mm
# line nn-mm -> lines~nn--mm  -- includes typo fix
# Line nn-mm -> Lines~nn--mm  -- includes typo fix
# line~nn-mm -> lines~nn--mm  -- includes typo fix
# Line~nn-mm -> Lines~nn--mm  -- includes typo fix
# Lines~nn--mm and oo-pp -> Lines~nn--mm and oo--pp
# Slides nn-mm -> Slides~nn--mm
# Figures~\ref{foo}-\ref{bar} -> Figures~\ref{foo}--\ref{bar}
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
# Copyright (C) Akira Yokosawa, 2016
#
# Authors: Akira Yokosawa <akiyks@gmain.com>

cat $1 |
	sed -e 's/Lines~\([0-9]\+\)-\([0-9]\+\)/Lines~\1--\2/g' \
	    -e 's/Lines \([0-9]\+\)-\([0-9]\+\)/Lines~\1--\2/g' \
	    -e 's/lines~\([0-9]\+\)-\([0-9]\+\)/lines~\1--\2/g' \
	    -e 's/lines \([0-9]\+\)-\([0-9]\+\)/lines~\1--\2/g' \
	    -e 's/Line~\([0-9]\+\)-\([0-9]\+\)/Lines~\1--\2/g' \
	    -e 's/Line \([0-9]\+\)-\([0-9]\+\)/Lines~\1--\2/g' \
	    -e 's/line~\([0-9]\+\)-\([0-9]\+\)/lines~\1--\2/g' \
	    -e 's/line \([0-9]\+\)-\([0-9]\+\)/lines~\1--\2/g' \
	    -e 's/Lines~\([0-9]\+\)--\([0-9]\+\) and \([0-9]\+\)-\([0-9]\+\)/Lines~\1--\2 and \3--\4/g' \
	    -e 's/Slides \([0-9]\+\)-\([0-9]\+\)/Slides~\1--\2/g' \
	    -e 's/Figures~\(\\ref{.*}\)-\(\\ref{.*}\)/Figures~\1--\2/g' \
	    -e 's/\/\* Lines~\([0-9]\+\)--\([0-9]\+\) \*\//\/\* Lines \1-\2 \*\//g'

# Last pattern is to preserve "Lines n-m" in comments within code snippet
