#!/bin/sh
#
# eps2pdf.sh: Convert all .eps files to .pdf for the benefit of pdflatex.
#	Also convert any .svg files to .pdf while we are at it.
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
# Copyright (c) 2010 Paul E. McKenney, IBM Corporation.

epsfiles=`find . -name '*.eps' -print`
for i in $epsfiles
do
	basename="${i%.eps}"
	if test ! -f "$basename.pdf" -o "$basename.eps" -nt "$basename.pdf"
	then
		echo "$basename.eps -> $basename.pdf"
		a2ping --below --hires --bboxfrom=compute-gs \
			"$basename.eps" "$basename.pdf"
	fi
done
svgfiles=`find . -name '*.svg' -print`
for i in $svgfiles
do
	basename="${i%.svg}"
	if test ! -f "$basename.pdf" -o "$basename.svg" -nt "$basename.pdf"
	then
		echo "$basename.svg -> $basename.pdf"
		inkscape --export-pdf=$basename.pdf $basename.svg
	fi
done
