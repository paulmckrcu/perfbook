#!/bin/sh
#
# Run the first round of pdflatex.
# It is assumed to be used together with runlatex.sh and invoked from
# 'make' command.
#
# Usage: sh runfirstlatex.sh file[.tex]
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
# Copyright (C) IBM Corporation, 2012
# Copyright (C) Akira Yokosawa, 2016
#
# Authors: Paul E. McKenney <paulmck@us.ibm.com>
#          Akira Yokosawa <akiyks@gmail.com>

if test -z "$1"
then
	echo No latex file specified, aborting.
	exit 1
fi

basename=`echo $1 | sed -e 's/\.tex$//'`

echo "pdflatex 1 for $basename.pdf"
pdflatex $basename > /dev/null 2>&1 < /dev/null || :
if grep -q '! Emergency stop.' $basename.log
then
	echo "----- Fatal latex error, see $basename.log for details. -----"
	exit 1
fi
grep 'Latex Warning:' $basename.log > $basename-warning.log
touch $basename-first.log
exit 0
