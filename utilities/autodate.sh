#!/bin/sh
#
# Extract git commit date info to generate autodate.tex.
# If invoked on not-clean git repository, append "(m)" to date field
# for title.
# If git status is not available, use current date instead.
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
# Copyright (C) Akira Yokosawa, 2017
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

export LC_TIME=C
# check if we are in git repository
if ! test -e .git
then
	date_str=`date -R`
	modified=""
	release=""
	commitid=""
else
	date_str=`git show --format="%cD" | head -1`
	# check if git status is clean
	gitstatus=`git status --porcelain | wc -l`
	if [ $gitstatus != "0" ]
	then
		modified="(m)"
	else
		modified=""
	fi
	description="`git describe --tags HEAD`"
	case "$description" in
	*-g*)
		release=`env printf 'Commit: \\\texttt{%s}' "$description"`
		commitid=`echo $description | sed -e 's/.*-\(g.*\)/\1/'`
		;;
	v*)
		release="Release $description"
		commitid=$description
		;;
	Edition*)
		release="Edition"
		commitid=$description
		case "$description" in
		*P*)
			release="Print $release"
			;;
		esac
		case "$description" in
		Edition[.-][0-9]*)
			ednum="`echo $description | sed -e 's/^Edition[.-]\([0-9]*\).*$/\1/'`"
			release=`env printf '\\Ordinalstringnum{%s} %s' $ednum "$release"`
			;;
		esac
		case "$description" in
		*-rc[0-9]*)
			rc="`echo $description | sed -e 's/^.*-rc\(.*\)$/\1/'`"
			release="$release, Release Candidate $rc"
			;;
		esac
		;;
	*)
		release=`env printf 'Tag: \\\texttt{%s}' "$description"`
		commitid=`echo $description | sed -e 's/.*-\(g.*\)/\1/'`
		;;
	esac
fi
month=`date --date="$date_str" +%B`
year=`date --date="$date_str" +%Y`
day=`date --date="$date_str" +%e`
if test -n "$release"
then
	release=`env printf '%s %s' '\\\\' "$release"`
fi

env printf '\\date{%s %s, %s %s %s}\n' $month $day $year "$release" $modified
env printf '\\newcommand{\\commityear}{%s}\n' $year
env printf '\\newcommand{\\commitid}{%s}\n' $commitid$modified
