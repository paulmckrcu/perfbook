# fixfonts.sh: Convert an .eps file to use embeddable fonts, taking from
#	standard input and putting on standar output.
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
# Copyright (c) 2011 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2018 Akira Yokosawa

sed	-e 's+Times-Roman-BoldItalic+NimbusSanL-BoldItal+g' \
	-e 's+Times-Roman-Italic+NimbusSanL-ReguItal+g' \
	-e 's+Times-Roman-Bold+NimbusSanL-Bold+g' \
	-e 's+Times-Roman+NimbusSanL-Regu+g' \
	-e 's+Times+NimbusSanL-Regu+g' \
	-e 's+Helvetica-BoldOblique+NimbusSanL-BoldItal+g' \
	-e 's+Helvetica-Oblique+NimbusSanL-ReguItal+g' \
	-e 's+Helvetica-Bold-iso+NimbusSanL-Bold+g' \
	-e 's+Helvetica-Bold+NimbusSanL-Bold+g' \
	-e 's+Helvetica-Narrow-BoldOblique-iso+NimbusSanL-BoldCondItal+g' \
	-e 's+Helvetica-Narrow-BoldOblique+NimbusSanL-BoldCondItal+g' \
	-e 's+Helvetica-Narrow-Oblique-iso+NimbusSanL-ReguCondItal+g' \
	-e 's+Helvetica-Narrow-Oblique+NimbusSanL-ReguCondItal+g' \
	-e 's+Helvetica-Narrow-Bold-iso+NimbusSanL-BoldCond+g' \
	-e 's+Helvetica-Narrow-Bold+NimbusSanL-BoldCond+g' \
	-e 's+Helvetica-Narrow-iso+NimbusSanL-ReguCond+g' \
	-e 's+Helvetica-Narrow+NimbusSanL-ReguCond+g' \
	-e 's+Helvetica-iso+NimbusSanL-Regu+g' \
	-e 's+Helvetica+NimbusSanL-Regu+g' \
	-e 's+Symbol+StandardSymL+g' \
	-e 's+Courier-BoldOblique+NimbusMonL-BoldObli+g' \
	-e 's+Courier-Oblique+NimbusMonL-ReguObli+g' \
	-e 's+Courier-Bold+NimbusMonL-Bold+g' \
	-e 's+Courier+NimbusMonL-Regu+g' \
	-e 's+NimbusSanL-Regu-Italic+NimbusSanL-ReguItal+g' \
	-e 's+NimbusSanL-Regu-BoldItalic+NimbusSanL-BoldItal+g' \
	-e 's+NimbusSanL-Regu-Bold+NimbusSanL-Bold+g' \
	-e 's+StardardSymL-+Symbol-+g'
