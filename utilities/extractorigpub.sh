#!/bin/sh
#
# Extracts Original Publications from the main latex document and transforms
# them to generate an list of citations indicating where a given section
# or appendix was originally published.
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
# Copyright (C) IBM Corporation, 2008-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

echo "% mainfile: perfbook.tex"
sed -n -e '/^\\OriginallyPublished{/p' \
       -e '/^\\RangeOriginallyPublished{/p' |
sed -e 's/^\\OriginallyPublished{/\\OrigPubItem{/' \
    -e 's/^\\RangeOriginallyPublished{/\\RangeOrigPub{/'
