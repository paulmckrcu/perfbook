#!/bin/sh
#
# Extract CONFIG variables from the specified files, or from RCU-related
# files if none specified.
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
# Copyright (C) IBM Corporation, 2008
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

files=${@-include/linux/rcu* kernel/rcu*}

grep '[^A-Z_0-9]CONFIG_[A-Z_0-9]*' $files |
	sed -e 's/CONFIG_[A-Z_0-9]*/&:/g' |
	tr ':' '\012' |
	grep '[^A-Z_0-9]CONFIG_[A-Z_0-9]*' |
	sed -e 's/^.*\(CONFIG_[A-Z_0-9]*\)/\1/g' |
	sort -u
