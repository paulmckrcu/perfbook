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
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright (c) 2010 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2016 Akira Yokosawa

if ! fc-list | grep -q steel
then
	echo "#######################################################################"
	echo "## Steel City Comic font is not found in the font cache!             ##"
	echo "## Some speech balloons in the cartoons would be rendered awkwardly.  ##"
	echo "## See item 1 in FAQ.txt for how to install the font.                ##"
	echo "## Nevertheless, this build will resume in a short while.            ##"
	echo "#######################################################################"
	sleep 5
fi

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
