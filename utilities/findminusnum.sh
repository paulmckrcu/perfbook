#!/bin/sh
#
# Find hypens used as minus signs in text mode
#
# This is an incomplete script.
# False positives will include those of verbatim and \co{} arguments.
# Use the result just for hints.
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

find . -name "*.tex" -exec grep -nH -E '[[:space:]+|\[|(]\-[0-9]+' {} + | \
grep -v "perfbook_flat.tex" | grep -v "qqz.tex" | grep -v "appendix/rcuimpl"
