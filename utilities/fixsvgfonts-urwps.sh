# SPDX-License-Identifier: GPL-2.0
#
# fixsvgfonts-urwps.sh: Convert an .svg file to use embeddable fonts,
#       taking from standard input and putting on standar output.
#
# Copyright (c) 2018 Akira Yokosawa

sed	-e 's+family:Helvetica+family:Nimbus Sans+g' \
	-e 's+family="Helvetica+family="Nimbus Sans+g' \
	-e 's+family:Sans+family:Nimbus Sans+g' \
	-e 's+cation:Sans+cation:Nimbus Sans+g' \
	-e 's+family:Courier+family:Nimbus Mono PS+g' \
	-e 's+family="Courier+family="Nimbus Mono PS+g' \
	-e 's+family:Symbol+family:Standard Symbols PS+g' \
	-e 's+cation:Symbol+cation:Standard Symbols PS+g' \
	-e 's+family:Nimbus Sans L+family:Nimbus Sans+g' \
	-e 's+family="Nimbus Sans L+family="Nimbus Sans+g' \
	-e 's+cation:Nimbus Sans L+cation:Nimbus Sans+g' \
	-e 's+family:Nimbus Mono L+family:Nimbus Mono PS+g' \
	-e 's+family="Nimbus Mono L+family="Nimbus Mono PS+g' \
	-e 's+cation:Nimbus Mono L+cation:Nimbus Mono PS+g' \
	-e 's+family:Standard Symbols L+family:Standard Symbols PS+g' \
	-e 's+cation:Standard Symbosl L+cation:Standard Symbols PS+g'
