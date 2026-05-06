#!/bin/sh
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Check buggy LaTeX packages observed in distro TeX Live as of April 2026.
#
# Copyright (C) Akira Yokosawa, 2026

: ${WARNEXIT:=1}

KPSEWHICH=`command -v kpsewhich`

if [ "$KPSEWHICH" != "" ] ; then

#### Is lineno.sty too young for LaTeX2e ?
# LaTeX2e <2025-06-01> and later needs lineno.sty v5.7 or later.
# This is a minor incompatibility observed only in twocolumn builds.
#
#   Symptom: chapter & section titles in header area are broken.

lineno_sty=`kpsewhich lineno.sty`
lineno_ver=`grep -F '\def\fileversion' $lineno_sty | \
	sed -E -e 's/.*\{(v[0-9\.]+)\}.*$/\1/'`
LINENO_AT_LEAST=v5.7
linenosince=`env printf "$LINENO_AT_LEAST\n$lineno_ver" | sort -V | head -n 1`

latex_release=`kpsewhich latexrelease.sty`
latex_ver=`grep -F -A1 -e '\edef\latexreleaseversion' $latex_release | \
	grep -F '{' | \
	sed -E -e 's/[ ]+\{([0-9\-]+)\}/<\1>/' -e 's/\//\-/g'`

LATEX_SINCE="<2025-06-01>"
latexsince=`env printf "$LATEX_SINCE\n$latex_ver" | sort | head -n 1`

if [ "$latexsince" = "$LATEX_SINCE" ] ; then  # older
    if [ "$linenosince" != "$LINENO_AT_LEAST" ] ; then
	echo "lineno.sty $lineno_ver is too young for LaTeX2e $latex_ver."
	echo "Upgrade lineno.sty to at least v5.7."
        echo "Treat this as a minor issue and continue building nonetheless."
    fi
fi

#### Is microtype.sty too young for recent hyperref (>=v7.01p) ?

microtype_sty=`kpsewhich microtype.sty`
microtype_ver=`grep -F -A2 -e '\ProvidesPackage' $microtype_sty | \
	grep -F '[' | \
	sed -E -e 's/[ ]+\[[0-9\/]+ (v[0-9a-z\.]+)/\1/'`

MICROTYPE_AT_LEAST="v3.2c"
microtypesince=`env printf "$MICROTYPE_AT_LEAST\n$microtype_ver" | sort -V | head -n 1`

hyperref_sty=`kpsewhich hyperref.sty`
hyperref_ver=`grep -F -A1 -e '\ProvidesPackage{hyperref}' $hyperref_sty | \
	grep -F '[' | sed -e 's/%//' | \
	sed -E -e 's/[ ]+\[[0-9\/\-]+ (v[0-9a-z\.]+)[ ]+/\1/'`

HYPERREF_SINCE="v7.01p"
hyperrefsince=`env printf "$HYPERREF_SINCE\n$hyperref_ver" | sort -V | head -n 1`

if [ "$hyperrefsince" = "$HYPERREF_SINCE" ] ; then  # older
    if [ "$microtypesince" != "$MICROTYPE_AT_LEAST" ] ; then
	echo "microtype.sty $microtype_ver is too young for hyperref.sty $hyperref_ver."
	echo "Upgrade microtype.sty to at least $MICROTYPE_AT_LEAST."
        echo "Treat this as a minor issue and continue building nonetheless."
    fi
fi

#### Tentative check of packaging inconsistency in Fedora 44 #############
# latex-base vs array (provided in texlive-tools)

latex_release_dev=`kpsewhich latex-dev/base/latexrelease.sty`

if [ "$latex_release_dev" != "" ] ; then
	latex_dev_ver=`grep -F -A1 -e '\edef\latexreleaseversion' $latex_release_dev | \
	grep -F '{' | \
	sed -E -e 's/[ ]+\{([0-9\-]+)\}/<\1>/' -e 's/\//\-/g'`
fi

array_sty=`kpsewhich array.sty`
array_req_ver=`grep -F -e '\NeedsTeXFormat{LaTeX2e}' $array_sty | \
	tail -n 1 | \
	sed -e 's/\\\\NeedsTeXFormat{LaTeX2e}//' | \
	sed -E -e 's/\[/</' -e 's/\]/>/' -e 's/\//\-/g'`

if [ "$LATEX" != "pdflatex-dev" ] ; then
    if [ "$array_req_ver" \> "$latex_ver" -a "$WARNEXIT" = "1" ] ; then
	echo "#### array.sty requires a later release of LaTeX2e.     ####"
	echo "#### arary.sty requires LaTeX2e $array_req_ver,           ####"
	echo "#### while your LaTeX2e is $latex_ver.                ####"
	echo "#### Check your TeX Live installation.  (Known issue under Fedora 44.)"
	echo "#### 1st option is to downgrade array.sty to v2.6n."
	echo "#### 2nd option is to install texlive-latex-base-dev and"
	echo "####     say 'make LATEX=pdflatex-dev'."
	echo "#### As a last resort, 'make WARNEXIT=0' would ignore such 'LaTeX Warning:'"
	echo "####     messages and complete iteration of latex runs (if you are lucky)."
	exit 1
    fi
else
    if [ "$latex_dev_ver" = "" ] ; then
	echo "#### LaTeX2e (-dev) is not found!                       ####"
	echo "#### You need to install texlive-latex-base-dev.        ####"
	exit 1
    fi
fi

fi  #KPSEWHICH
