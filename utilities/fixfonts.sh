# fixfonts.sh: Convert the specified .eps file to use embeddable fonts.
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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
#
# Copyright (c) 2011 Paul E. McKenney, IBM Corporation.

sed	-e 's+Times-Roman+NimbusSanL-Regu+g' \
	-e 's+Times+NimbusSanL-Regu+g' \
	-e 's+Helvetica-BoldOblique+NimbusSanL-BoldItal+g' \
	-e 's+Helvetica-Oblique+NimbusSanL-ReguItal+g' \
	-e 's+Helvetica-Bold+NimbusSanL-Bold+g' \
	-e 's+Helvetica-Bold-iso+NimbusSanL-Bold+g' \
	-e 's+Helvetica+NimbusSanL-Regu+g' \
	-e 's+Helvetica-iso+NimbusSanL-Regu+g' \
	-e 's+Symbol+StandardSymL+g' \
	-e 's+Courier+NimbusMonL-Regu+g' \
	-e 's+Courier-Bold+NimbusMonL-Bold+g' \
	-e 's+Courier-Oblique+NimbusMonL-ReguObli+g' \
	-e 's+Courier-BoldOblique+NimbusMonL-BoldObli+g'
