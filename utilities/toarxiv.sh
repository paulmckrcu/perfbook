#!/bin/sh
#
# toarxiv.sh: Create a directory containing the pieces of perfbook
#	needed for an arxiv.org submission.  Run at the top level of
#	the perfbook source tree.
#
# Usage: toarxiv.sh [ destdir ]
#
# The destdir argument defaults to "/tmp/perfbook".  If this already
# exists, the script complains and aborts.
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
# Copyright (c) 2017 Paul E. McKenney, IBM Corporation.

destdir=${1-/tmp/perfbook}
if test -e ${destdir}
then
	echo Destination \"${destdir}\" already exists, aborting!
	exit 1
fi
if mkdir ${destdir}
then
	:
else
	echo Could not create \"${destdir}\", aborting!
	exit 1
fi
make

find */ -type d -print |
	grep -v '^\.git' |
	grep -v '\.git/' |
	grep -v '\.git$' |
	grep -v '^utilities' |
	sed -e "s,^,mkdir ${destdir}/," |
	sh

cp autodate.tex glossary.tex origpub.tex contrib.tex legal.tex qqz.tex origpub.sty qqz.sty perfbook.bbl ${destdir}

find */ '(' -name '*.pdf' -o -name '*.tex' ')' -exec cp {} ${destdir}/{} \;

# Remove "helper" .tex files that generate figure (keep PDF instead)
rm ${destdir}/SMPdesign/DiningPhilosopher4part-b.tex
rm ${destdir}/SMPdesign/DiningPhilosopher5.tex
rm ${destdir}/SMPdesign/DiningPhilosopher5PEM.tex
rm ${destdir}/SMPdesign/DiningPhilosopher5TB.tex

# The following changes work around arxiv.org limitations
sed	-e '/usepackage{footnotebackref}/d' \
	-e 's/\[bookmarks=true,bookmarksnumbered=true,pdfborder={0 0 0}]/[bookmarks=false]/' \
	< perfbook.tex > ${destdir}/perfbook.tex
echo "nohypertex" > ${destdir}/00README.XXX
