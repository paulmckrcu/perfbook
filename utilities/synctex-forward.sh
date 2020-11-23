#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Set "% mainfile:" lines with proper "% mainfile: <...>" tags in
# sub .tex files.
#
# With no argument, the main file will be "perfbook.tex",
# which will do nothing by default.
# With abbrev target such as "1c", "hb", and so on, the main file
# will be "perfbook-1c.tex", perfbook-hb.tex", and so on.
#
# Depth of subdirectory is deduced from the path of each sub .tex file.
#
# Changes made by this script can be reverted by running without
# argument.
#
# WARNING: By runnig this script, your working tree will be modified.
# It is highly recommented to commit your changes before running
# this script.

# If LATEX_OPT does not have "synctex", do nothing
if ! echo $LATEX_OPT | grep -q synctex ; then
	echo "LATEX_OPT has no synctex option. Exiting..."
	echo "See #11 in FAQ-BUILD.txt for SyncTeX support."
	exit 1
fi

# warn if git status is not clean later
gitstatus=`git status --porcelain | wc -l`
if [ $gitstatus != "0" ] ; then
	wasnotclean=1
else
	wasnotclean=0
fi

if [ $# -eq 0 ] ; then
	main="perfbook.tex"
	change="reverted"
else
	case $1 in
	2c)
		main="perfbook.tex"
		change="reverted"
		;;
	1c|hb|a4|tcb|msnt|mstx|msr|msn|sf|msns|mss|qq|nq|ix)
		main="perfbook-$1.tex"
		change="modified"
		;;
	1ctcb|1cmsnt|1cmstx|1cmsr|1cmsn|1csf|1cmsns|1cmss|1cqq|1cnq|1cix)
		main="perfbook-$1.tex"
		change="modified"
		;;
	*)
		echo "Unknown target!!"
		exit 1
		;;
	esac
fi

tmpf=`mktemp`
texfiles=`find . -name '*.tex' -print`
modified=0
for i in $texfiles
do
	c=$(expr `echo $i | grep -o "/" | wc -l` - 1)
	x=
	for j in $(seq 1 $c)
	do
		x=..\\/$x
	done
	mainpath=$x$main
	pattern="s/% mainfile: .*perfbook.*\.tex/% mainfile: $mainpath/"
	cat $i | sed -e "$pattern" > $tmpf
	if ! diff -q $i $tmpf >/dev/null ; then
		echo "$i $change."
		cp -f $tmpf $i
		modified=1
	fi
done

if [ $modified -eq 0 ] ; then
	echo "No modification."
else
	if [ $main != "perfbook.tex" -a $wasnotclean -eq 1 ] ; then
		echo "### Git status was not clean."
		echo "### To revert the changes, just run '$0'."
	fi
fi

# check if synctex database exists
mainbase="${main%.tex}"
if [ `ls -1 perfbook* | grep -c $mainbase.synctex` -eq 0 ] ; then
	echo "### $mainbase.synctex*: file not found."
	echo "### See #11 in FAQ-BUILD.txt for how to generate one."
fi
