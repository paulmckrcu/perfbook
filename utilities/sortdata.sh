#!/bin/sh
#
# Input a file where each line has an x-value followed by a series of
# y-values.  Output each line in order, but with the y-values on each
# sorted within that line.
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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
#
# Copyright (C) IBM Corporation, 2012
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

awk '{
	for (i = 2; i <= NF; i++)
		a[i - 1] = $i;
	asort(a);
	s = $1;
	for (i = 2; i <= NF; i++)
		s = s " " a[i - 1];
	print s;
}'
