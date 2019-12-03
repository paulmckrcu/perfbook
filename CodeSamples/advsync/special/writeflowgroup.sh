#!/bin/sh
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
# Copyright (C) IBM Corporation, 2007-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@us.ibm.com>

awk '
BEGIN	{
		maxcpu = -1;
	}
	{
		cpu[$1] = $2;
		if (maxcpu < $1) {
			maxcpu = $1;
		}
		node = "";
		for (i = 0; i <= maxcpu; i++) {
			if (cpu[i] == $2) {
				node = node " " i;
			}
		}
		print $3, $2 " " node "  (" $1 ")";
	}'
