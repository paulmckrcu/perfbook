#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Check if commands grep, sed, and date can be used for
# building perfbook.
#
# Copyright (C) Akira Yokosawa, 2023

export LC_TIME=C

: ${SED:=sed}
: ${DATE:=date}
: ${VERBOSE:=}
: ${WHICH:=command -v}

fatal=""

# test sed (repeat pattern \? and \+)
sed_result=""
sed_out=`echo aaabbc | $SED -e 's/[ab]\+c\?//'`
if [ "$sed_out" = "" ] ; then
	sed_result="OK"
else
	sed_result="NG"
	fatal="sed $fatal"
fi

# test date (format conversion)
date_result=""
date_str="Tue, 10 Jan 2023 00:00:00 +0000"
if month=`$DATE -d "$date_str" +%B 2>/dev/null` ; then
	date_flavor="GNU date"
else
	if month=`$DATE -jR -f "%a, %d %b %Y %T %z" "$date_str" +%B 2>/dev/null` ;
	then
		date_flavor="BSD date"
	else
		date_flavor="Unknown"
		fatal="date $fatal"
	fi
fi
if [ "$month" = "January" ] ; then
	date_result="OK"
else
	date_result="NG"
	fatal="date-format $fatal"
fi

# test availability of ptmro7t.tfm and pst-tools.sty
# (to cope with Fedora 44's change in package dependencies)

KPSEWHICH=`$WHICH kpsewhich`

if [ "$KPSEWHICH" != "" ] ; then
	ptmro7t_tfm=`$KPSEWHICH ptmro7t.tfm`
	pst_tools_sty=`$KPSEWHICH pst-tools.sty`
	if [ "$ptmro7t_tfm" = "" ] ; then
		ptmro7t_result="NG"
		fatal="ptmro7t.tfm $fatal"
	else
		ptmro7t_result="OK"
	fi
	if [ "$pst_tools_sty" = "" ] ; then
		pst_tools_result="NG"
		fatal="pst-tools.sty $fatal"
	else
		pst_tools_result="OK"
	fi
fi	

if [ "$fatal" = "" -a "$VERBOSE" = "" ] ; then
	exit 0
fi

# print results if any missing feature is detected
echo "==========================================="
echo "  preparatory test of necessary features   "
echo "==========================================="

if [ "$sed_result" != "OK" -o "$VERBOSE" != "" ] ; then
	echo
	echo '------------------------------------------'
	echo ' testing sed (repeat patterns \? and \+)  '
	echo '------------------------------------------'
	if [ "$sed_result" = "OK" ] ; then
		echo "OK."
	else
		echo "$SED (at `$WHICH $SED`) failed the test!"
	fi
fi
if [ "$date_result" != "OK" -o "$VERBOSE" != "" ] ; then
	echo
	echo "------------------------------------------"
	echo " testing date (format conversion)         "
	echo "------------------------------------------"
	echo -n "$date_flavor ... "
	if [ "$date_flavor" = "Unknown" ] ; then
		echo
		echo "Unknown date command found at `$WHICH $DATE`."
	else
		if [ "$month" = "January" ] ; then
			echo "OK."
		else
			echo "Hmm, something is wrong with format conversion"
			echo "$month"
		fi
	fi
fi
if [ "$ptmro7t_result" != "OK" ] ; then
	echo
	echo "------------------------------------------"
	echo " testing ptmro7t.tfm                      "
	echo "------------------------------------------"
	echo "ptmro7t.tfm ...  Not found!"
	echo "Please install texlive-collection-fontsrecommended."
fi
if [ "$pst_tools_result" != "OK" ] ; then
	echo
	echo "------------------------------------------"
	echo " testing pst-tools.sty                    "
	echo "------------------------------------------"
	echo "pst-tools.sty ...  Not found!"
	echo "Please install texlive-collection-pstricks."
fi
if [ "$fatal" != "" ] ; then
	echo
	echo "See #14 in FAQ-BUILD.txt for further info."
	echo "fatal: $fatal"
	exit 1
fi
