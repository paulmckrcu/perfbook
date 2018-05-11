# SPDX-License-Identifier: GPL-2.0
#
# fixsvgfonts.sh: Convert an .svg file to use embeddable fonts, taking from
#	standard input and putting on standard output.
#
# Copyright (c) 2018 Akira Yokosawa

sed	-e 's+family:Helvetica+family:Nimbus Sans L+g' \
	-e 's+family="Helvetica+family="Nimbus Sans L+g' \
	-e 's+family:Sans+family:Nimbus Sans L+g' \
	-e 's+cation:Sans+cation:Nimbus Sans L+g' \
	-e 's+family:Courier+family:Nimbus Mono L+g' \
	-e 's+family="Courier+family="Nimbus Mono L+g' \
	-e 's+family:Symbol+family:Standard Symbols L+g' \
	-e 's+cation:Symbol+cation:Standard Symbols L+g'
