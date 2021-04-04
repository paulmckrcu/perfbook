#!/bin/bash

if [ $# -ne 1 ]
then
	echo "Usage: $0 <package name>"
	exit 1
fi

package=$1

packages="titlesec cleveref listings draftwatermark epigraph fvextra glossaries-extra"
supported="false"
for p in $packages
do
	if [ "$package" == "$p" ]
	then
		supported="true"
		break
	fi
done
if [ "$supported" == "false" ]
then
	echo "$package is not supported"
	exit 1
fi

wget "http://mirrors.ctan.org/macros/latex/contrib/$package.zip"
unzip "$package.zip"
cd "$package" || exit 1

latex "$package.ins"
if [ ! -e "$package.sty" ]
then
	echo "$package.sty creation failed"
	exit 1
fi

install_dir=~/texmf/tex/latex/"$package"
mkdir -p "$install_dir"
cp *.sty "$install_dir/"
texhash ~/texmf

cd .. || exit 1
rm -fr "$package" "$package.zip"
