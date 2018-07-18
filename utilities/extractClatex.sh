#!/bin/bash
#
# Extracts marked code fragments and places them into files specified by
# the markings.
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
# Copyright (C) IBM Corporation, 2007
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

if test "$1" = ""
then
	cat
else
	cat "$@"
fi |
awk	'
BEGIN	{
	state = "scanning";
	}

	{
	if (state == "scanning") {
		if ($1 == "%CODE%") {
			state = "find-verbatim";
			filename = $2;
			if (fns[filename] == 1) {
				print "echo Warning: duplicate filename: " $2;
			}
			fns[filename] = 1;
		}
	} else if (state == "find-verbatim") {
		if ($1 == "\\begin{verbatim}") {
			state = "copy-code";
			print "cat > " filename " << '"'"'@@@EOF@@@'"'"'";
		}
	} else if (state == "copy-code") {
		if ($1 != "\\end{verbatim}") {
			print substr($0, 5);
		} else {
			print "@@@EOF@@@";
			state = "scanning";
		}
	}
	}' | sh
