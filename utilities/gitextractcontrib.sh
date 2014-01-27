#!/bin/sh
#
# Extracts contributors' email addresses from the git logs.
#
# Usage: sh gitextractcontrib.sh [first[..last]]
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
# Copyright (C) IBM Corporation, 2008
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

git log $1 | egrep '^ *(Signed-off-by|Reported-by)' |
	sed -e 's/ *Signed-off-by: *//' -e 's/ *Reported-by: *//' |
	sort -u | grep -v "Paul E. McKenney" |
	sed -e 's/\([^<]*\)<\([^>]*\)>/\2 \1/' | sed -e 's/ *$//' |
	sort -u -k1
