#!/bin/sh
# SPDX-License-Identifier: GPL-2.0
#
# Regression test of parallel pdflatex runs.
# Copyright (C) Akira Yokosawa, 2022
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

TARGETS=${TARGETS:-2c 1c eb}
JOBS=${JOBS:-4}
TMP=${TMP:-/tmp}
REFMAKE=${REFMAKE:-make -f Makefile.2022.01.25}
export LATEX_OPT=-synctex=1

copy_synctex_db () {
	for t in $TARGETS
	do
		case $t in
			2c ) base=perfbook;;
			*  ) base=perfbook-$t;;
		esac
		cp $base.synctex.gz $TMP/$base.$1.synctex.gz
	done
}

# Reference sequential builds

$REFMAKE neatfreak
$REFMAKE -j$JOBS perfbook_flat.tex
$REFMAKE $TARGETS

copy_synctex_db ref

# Sequential builds

make neatfreak
make -j$JOBS perfbook_flat.tex
make $TARGETS

copy_synctex_db sequ

# Parallel builds

make neatfreak
make -j$JOBS $TARGETS

copy_synctex_db para

cmp_err=0

for t in $TARGETS
do
	case $t in
		2c ) base=perfbook;;
		*  ) base=perfbook-$t;;
	esac

	if ! cmp $TMP/$base.ref.synctex.gz $TMP/$base.sequ.synctex.gz
	then
		cmp_err=`expr $cmp_err + 1`
	fi
	if ! cmp $TMP/$base.ref.synctex.gz $TMP/$base.para.synctex.gz
	then
		cmp_err=`expr $cmp_err + 1`
	fi
done

if test $cmp_err -eq 0
then
	echo "No mismatch detected in SyncTeX databases."
	exit 0
else
	echo "Mismatch detected in SyncTeX databases!"
	exit 1
fi
