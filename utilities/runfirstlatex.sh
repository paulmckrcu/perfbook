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
# Copyright (C) IBM Corporation, 2012-2019
# Copyright (C) Facebook, 2019
# Copyright (C) Akira Yokosawa, 2016, 2023
#
# Authors: Paul E. McKenney <paulmck@us.ibm.com>
#          Akira Yokosawa <akiyks@gmail.com>

if test -z "$1"
then
	echo No latex file specified, aborting.
	exit 1
fi

if ! sh utilities/mpostcheck.sh
then
	exit 1
fi

# newtx font package version check (newer or equal to Ubuntu 14.04)
NEWTXTEXT=`kpsewhich newtxtext.sty`
NEWTXTEXT_DATE=`grep filedate $NEWTXTEXT | grep -o -E "[/0-9]*"`
# We need TeX Live 2013/Debian (Ubuntu 14.04) or later
if [ "$NEWTXTEXT_DATE" \< "2014/02/12" ]
then
	echo "############################################################"
	echo "### Old version of font package 'newtx' is detected.     ###"
	echo "### You need to upgrade your TeX Live installation.      ###"
	echo "### See item 9 in FAQ-BUILD.txt for further info.        ###"
	echo "############################################################"
	exit 1
fi

DETECTED_BUGGY=0
# listings package version check (TeX Live 2014 and 2015 had buggy ones)
if grep -F "fileversion" `kpsewhich listings.sty` | grep -q -E "1.5[cde]"
then
	echo "############################################################"
	echo "### Buggy version of LaTeX package 'listings' detected!! ###"
	echo "### (Known issue in TeX Live 2014 and 2015)              ###"
	echo "### Please install a latest version.                     ###"
	echo "### See item 10 in FAQ-BUILD.txt for further info.       ###"
	echo "############################################################"
	DETECTED_BUGGY=1
fi

basename=`echo $1 | sed -e 's/\.tex$//'`

: ${LATEX:=pdflatex}

echo "$LATEX 1 for $basename.pdf"
$LATEX $LATEX_OPT $basename > /dev/null 2>&1 < /dev/null
exitcode=$?
ENCGUESS_CMD=`command -v encguess`
if [ "x$ENCGUESS_CMD" != "x" ]
then
	if encguess -s iso-8859-1 $basename.log | grep -q ISO-8859-1
	then
		mv $basename.log $basename-tmp.log
		iconv -f ISO-8859-1 -t UTF-8 $basename-tmp.log > $basename.log
		rm $basename-tmp.log
	fi
fi
if grep -q 'LaTeX Warning: You have requested' $basename.log
then
	grep -A 4 'LaTeX Warning: You have requested' $basename.log
	echo "### Incompatible package(s) detected. See $basename.log for details. ###"
	echo "### See items 9 and 10 in FAQ-BUILD.txt for how to update.          ###"
	exit 1
fi
if grep -q 'LaTeX Error:' $basename.log
then
	echo "----- !!! Fatal latex error !!! -----"
	grep -B 5 -A 8 'LaTeX Error:' $basename.log
	echo "----- See $basename.log for the full log. -----"
	exit 2
fi
if grep -q 'pdfTeX error:' $basename.log
then
	echo "----- !!! Fatal pdfTeX error !!! -----"
	grep -B 10 -A 8 '!pdfTeX error:' $basename.log
	echo "----- See $basename.log for the full log. -----"
	exit 2
fi
if grep -q '! Emergency stop.' $basename.log
then
	grep -B 10 -A 5 '! Emergency stop.' $basename.log
	echo "----- Fatal latex error, see $basename.log for details. -----"
	exit 2
fi
if [ $exitcode -ne 0 ]; then
	tail -n 20 $basename.log
	echo "\n!!! $LATEX aborted !!!"
	exit $exitcode
fi
if [ $DETECTED_BUGGY -eq 1 ]; then
	exit 1
fi
grep 'LaTeX Warning:' $basename.log > $basename-warning.log
touch $basename-first.log
exit 0
