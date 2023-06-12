# SPDX-License-Identifier: GPL-2.0
#
# fixsvgfonts-urwps.sh: Convert an .svg file to use embeddable fonts,
#       taking from standard input and putting on standard output.
#
# Copyright (c) 2018, 2021 Akira Yokosawa

sed	-e 's+:Helvetica+:Nimbus Sans+g' \
	-e 's+="Helvetica+="Nimbus Sans+g' \
	-e 's+:Sans+:Nimbus Sans+g' \
	-e 's+:sans-serif+:DejaVu Sans+g' \
	-e 's+:Courier+:Nimbus Mono PS+g' \
	-e 's+="Courier+="Nimbus Mono PS+g' \
	-e 's+:monospace+:DejaVu Sans Mono+g' \
	-e 's+monospace,+DejaVu Sans Mono,+g' \
	-e 's+:Symbol+:FreeSans+g' \
	-e 's+:Nimbus Sans L+:Nimbus Sans+g' \
	-e 's+="Nimbus Sans L+="Nimbus Sans+g' \
	-e 's+:Nimbus Mono L+:Nimbus Mono PS+g' \
	-e 's+="Nimbus Mono L+="Nimbus Mono PS+g' \
	-e 's+:URW Gothic L+:URW Gothic+g' \
	-e 's+="URW Gothic L+="URW Gothic+g'
