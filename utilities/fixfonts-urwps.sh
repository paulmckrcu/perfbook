# fixfonts-urwps.sh: Convert an .eps file to use embeddable fonts, taking from
#	standard input and putting on standar output.
#
# Based on fixfonts.sh, updated for Fedora 27 by Akira Yokosawa.
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
# Copyright (c) 2018 Akira Yokosawa.

sed	-e 's+Times-Roman-BoldItalic+NimbusSans-BoldItalic+g' \
	-e 's+Times-Roman-Italic+NimbusSans-Italic+g' \
	-e 's+Times-Roman-Bold+NimbusSans-Bold+g' \
	-e 's+Times-Roman+NimbusSans-Regular+g' \
	-e 's+Times+NimbusSans-Regular+g' \
	-e 's+Helvetica-BoldOblique+NimbusSans-BoldItalic+g' \
	-e 's+Helvetica-Oblique+NimbusSans-Italic+g' \
	-e 's+Helvetica-Bold-iso+NimbusSans-Bold+g' \
	-e 's+Helvetica-Bold+NimbusSans-Bold+g' \
	-e 's+Helvetica-Narrow-BoldOblique-iso+NimbusSansNarrow-BdOblique+g' \
	-e 's+Helvetica-Narrow-BoldOblique+NimbusSansNarrow-BdOblique+g' \
	-e 's+Helvetica-Narrow-Oblique-iso+NimbusSansNarrow-Oblique+g' \
	-e 's+Helvetica-Narrow-Oblique+NimbusSansNarrow-Oblique+g' \
	-e 's+Helvetica-Narrow-Bold-iso+NimbusSansNarrow-Bold+g' \
	-e 's+Helvetica-Narrow-Bold+NimbusSansNarrow-Bold+g' \
	-e 's+Helvetica-Narrow-iso+NimbusSansNarrow-Regular+g' \
	-e 's+Helvetica-Narrow+NimbusSansNarrow-Regular+g' \
	-e 's+Helvetica-iso+NimbusSans-Regular+g' \
	-e 's+Helvetica+NimbusSans-Regular+g' \
	-e 's+Symbol+StandardSymbolsPS+g' \
	-e 's+Courier-BoldOblique+NimbusMonoPS-BoldItalic+g' \
	-e 's+Courier-Oblique+NimbusMonoPS-Italic+g' \
	-e 's+Courier-Bold+NimbusMonoPS-Bold+g' \
	-e 's+Courier+NimbusMonoPS-Regular+g' \
	-e 's+NimbusSanL-BoldItal+NimbusSans-BoldItalic+g' \
	-e 's+NimbusSanL-ReguItal+NimbusSans-Italic+g' \
	-e 's+NimbusSanL-Bold+NimbusSans-Bold+g' \
	-e 's+NimbusSanL-Regu+NimbusSans-Regular+g' \
	-e 's+NimbusMonL-BoldObli+NimbusMonoPS-BoldItalic+g' \
	-e 's+NimbusMonL-ReguObli+NimbusMonoPS-Italic+g' \
	-e 's+NimbusMonL-Bold+NimbusMonoPS-Bold+g' \
	-e 's+NimbusMonL-Regu+NimbusMonoPS-Regular+g' \
	-e 's+StandardSymL+StandardSymbolsPS+g' \
	-e 's+NimbusMono-Regular-Bold+NimbusMonoPS-Bold+g' \
	-e 's+NimbusMono-Regular+NimbusMonoPS-Regular+g' \
	-e 's+NimbusSans-Regular-Italic+NimbusSans-Italic+g' \
	-e 's+NimbusSans-Regular-BoldItalic+NimbusSans-BoldItalic+g' \
	-e 's+NimbusSans-Regular-Bold+NimbusSans-Bold+g' \
	-e 's+StandardSymbolsPS-+Symbol-+g'
