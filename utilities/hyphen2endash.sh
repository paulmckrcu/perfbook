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
# Slides nn-mm -> Slides~nn--mm
# CPUs~nn-mm -> CPUs~nn--mm
# CPUs nn-mm -> CPUs~nn--mm
# and nn-mm -> and~nn--mm
# and~nn-mm -> and~nn--mm
# Figures~\ref{foo}-\ref{bar} -> Figures~\ref{foo}--\ref{bar}
# \co{xxx}-\{yyy} -> \co{xxx}--\co{yyy}
# yyyy-\commityear -> yyyy--\commityear (in Legal statement)
# nn-mm~nanosecond -> nn--mm~nanosecond
# nn-mm~microsecond -> nn--mm~microsecond
# nn-mm~millisecond -> nn--mm~millisecond
# nn-mm~\emp -> nn--mm~\emp
# nn-mm days -> nn--mm~days
# nn-mm~days -> nn--mm~days
# nn-mm sheets -> nn--mm~sheets
# nn-mm~sheets -> nn--mm~sheets
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
# Copyright (C) Akira Yokosawa, 2016, 2017
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

cat $1 |
	sed -e 's/\([Ll]ines\?\)[ ~]\([0-9]\+\)-\([0-9]\+\)/\1~\2--\3/g' \
	    -e 's/Slides \([0-9]\+\)-\([0-9]\+\)/Slides~\1--\2/g' \
	    -e 's/Figures~\(\\ref{[^}]*}\)-\(\\ref{[^}]*}\)/Figures~\1--\2/g' \
	    -e 's/CPUs[ ~]\([0-9]\+\)-\([0-9]\+\)/CPUs~\1--\2/g' \
	    -e 's/and[ ~]\([0-9]\+\)-\([0-9]\+\)/and~\1--\2/g' \
	    -e 's/\(\\co{[^}]*}\)-\(\\co{[^}]*}\)/\1--\2/g' \
	    -e 's/\([0-9]\)-\(\\commityear\)/\1--\2/g' \
	    -e 's/\([0-9]\+\)-\([0-9]\+\)~nanosecond/\1--\2~nanosecond/g' \
	    -e 's/\([0-9]\+\)-\([0-9]\+\)~microsecond/\1--\2~microsecond/g' \
	    -e 's/\([0-9]\+\)-\([0-9]\+\)~millisecond/\1--\2~millisecond/g' \
	    -e 's/\([0-9]\+\)-\([0-9]\+\)~\\emp/\1--\2~\\emp/g' \
	    -e 's/\([0-9]\+\)-\([0-9]\+\)[ ~]days/\1--\2~days/g' \
	    -e 's/\([0-9]\+\)-\([0-9]\+\)[ ~]sheets/\1--\2~sheets/g' \
	    -e 's/\/\* Lines~\([0-9]\+\)--\([0-9]\+\) \*\//\/\* Lines \1-\2 \*\//g'

# Last pattern is to preserve "Lines n-m" in comments within code snippet
