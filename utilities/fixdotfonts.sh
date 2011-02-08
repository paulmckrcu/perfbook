# fixdotfonts.sh: Convert all .eps files produced by dot (graphviz) to
#	use embeddable fonts.
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
# Copyright (c) 2010 Paul E. McKenney, IBM Corporation.

names=`find . -name '*.dot' -print`
for i in $names
do
	basename="${i%.dot}"
	if test -f "$basename.eps"
	then
		if grep -q Nimbus "$basename.eps"
		then
			:
		else
			mv "$basename.eps" "$basename.eps.badfonts"
			sh utilities/fixfonts.sh < "$basename.eps.badfonts" \
						 > "$basename.eps"
			rm "$basename.eps.badfonts"
		fi
	fi
done
