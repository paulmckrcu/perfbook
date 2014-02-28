#!/bin/sh
#
# Run latex on the specified file and bibliography directory.
# Attempt to avoid useless repeats.
#
# Usage: runlatex.sh file.tex [ bibdir ]
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
# Authors: Paul E. McKenney <paulmck@us.ibm.com>

if test -z "$1"
then
	echo No latex file, aborting.
	exit 1
fi

basename=`echo $1 | sed -e 's/\.tex$//'`

iter=1
echo "pdflatex $iter"
pdflatex $basename > /dev/null 2>&1 < /dev/null || :
if grep -q '! Emergency stop.' $basename.log
then
	echo "----- Fatal latex error, see $basename.log for details. -----"
fi
if grep -q 'LaTeX Warning: There were undefined references' $basename.log
then
	if test -d "$2"
	then
		bibtex $basename || :
	else
		echo "No bibliography directory, skipping bibtex."
	fi
fi
while grep -q 'LaTeX Warning: Label(s) may have changed. Rerun to get cross-references right.' $basename.log
do
	iter=`expr $iter + 1`
	echo "pdflatex $iter"
	pdflatex $basename > /dev/null 2>&1 < /dev/null || :
	if grep -q '! Emergency stop.' $basename.log
	then
		echo "----- Fatal latex error, see $basename.log for details. -----"
	fi
	if test "$iter" -eq 4
	then
		echo "Iteration limit: $iter passes through pdflatex"
		exit 1
	fi
done
grep "LaTeX Warning:" $basename.log
exit 0
