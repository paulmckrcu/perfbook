#!/bin/sh
#
# gethashplots.sh: Copy up hash plots with specified tag.
#	Specify the date tag (e.g., 2013.12.02a) and run
#	in the top-level directory.
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
# Copyright (c) 2013-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

tag="$1"

cp CodeSamples/datastruct/data/hash.${tag}/*.eps datastruct
echo Hashing plots obtained from: > datastruct/hashtag.txt
echo CodeSamples/datastruct/data/hash.${tag} >> datastruct/hashtag.txt
