#!/bin/sh
#
# toarxiv.sh: Create a directory containing the pieces of perfbook
#	needed for an arxiv.org submission.  Run at the top level of
#	the perfbook source tree after typing "make".
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
# Copyright (c) 2017-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

T=/tmp/toarxiv.$$
trap 'rm -rf $T' 0 2
mkdir $T

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

cp autodate.tex glossary.tex origpub.tex contrib.tex legal.tex qqz.tex origpub.sty qqz.sty pfbook.cls pfhyphex.tex perfbook.bbl ${destdir}
cp `kpsewhich fvextra.sty` ${destdir}
cp `kpsewhich epigraph.sty` ${destdir}

find */ '(' -name '*.pdf' -o -name '*.lst' ')' -exec cp {} ${destdir}/{} \;

# Arxiv doesn't like "@" in filenames, so transform them to "=".
transform_fcv()
{
	sed -e 's/^\(\\input.*\)@\(.*.fcv\)/\1=\2/' < $1 > ${destdir}/$1
}
find */ -name '*.tex' -print |
	sed -e 's/^.*$/transform_fcv &/' > $T/texfiles
. $T/texfiles
find */ -name '*.fcv' -print |
	sed -e 's,^\(.*\)@\(.*\.fcv\),cp & '"${destdir}"'/\1=\2,' | sh

# A few code files.  This might end up not scaling, but...
cp appendix/styleguide/samplecodesnippet.c ${destdir}/appendix/styleguide

# Remove "helper" .tex files that generate figure (keep PDF instead)
rm ${destdir}/SMPdesign/DiningPhilosopher4part-b.tex
rm ${destdir}/SMPdesign/DiningPhilosopher5.tex
rm ${destdir}/SMPdesign/DiningPhilosopher5PEM.tex
rm ${destdir}/SMPdesign/DiningPhilosopher5TB.tex

# The following changes work around arxiv.org limitations
sed	-e '/usepackage{footnotebackref}/d' \
	-e 's/{toarxiv}{false}/{toarxiv}{true}/' \
	< perfbook.tex > ${destdir}/perfbook.tex
# echo "nohypertex" > ${destdir}/00README.XXX
