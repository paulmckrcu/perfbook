# SPDX-License-Identifier: GPL-2.0
#
# fixsvgfonts.sh: Convert an .svg file to use embeddable fonts, taking from
#	standard input and putting on standard output.
#
# Copyright (c) 2018, 2021 Akira Yokosawa

sed	-e 's+:Helvetica+:Nimbus Sans L+g' \
	-e 's+="Helvetica+="Nimbus Sans L+g' \
	-e 's+:Sans+:Nimbus Sans L+g' \
	-e 's+:sans-serif+:DejaVu Sans+g' \
	-e 's+:Courier+:Nimbus Mono L+g' \
	-e 's+="Courier+="Nimbus Mono L+g' \
	-e 's+:monospace+:DejaVu Sans Mono+g' \
	-e 's+monospace,+DejaVu Sans Mono,+g' \
	-e 's+:Symbol+:FreeSans+g'
