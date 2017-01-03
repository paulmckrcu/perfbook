#!/bin/sh
#
# Find hyphens used for number range and replace them with en dashes.
# (for bibliography pages field, conversion to en dash is done by BiBTeX)
#
# Replacement candidate
#   Volumes mm-nn -> Volumes mm--nn
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
# Copyright (C) Akira Yokosawa, 2017
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

cat $1 | sed -e 's/Volumes \([0-9]\+\)-\([0-9]\+\)/Volumes \1--\2/g'
