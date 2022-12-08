#!/bin/sh
#
# Usage: timeskewhist.sh < timeskew-output
#
# This script generates a histogram of the wall-clock/mono deviations.
# These are uncorrected, with the monotonic reading having been taken
# just before the wall-clock reading.  Props to stackoverflow user hsxz.
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
# Copyright (C) Facebook, 2022
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

fontsize=10
plotsize=0.7
min=-100
max=50

T="`mktemp -d ${TMPDIR-/tmp}/timeskewhist.sh.XXXXXX`"
trap 'rm -rf $T' 0

gawk '$1 + 0 != 0 { print $5 * 1000. * 1000. * 1000.; }' |
	gawk -v min="$min" -v max="${max}" > $T/wc-mono.dat '$1 >= min && $1 <= max { print; }'

cat << __EOF__ > $T/hist.gnuplot
set term postscript portrait ${fontsize} enhanced "NimbusSanL-Regu" fontfile "/home/git/perfbook/fonts/uhvr8a.pfb"
set size square ${plotsize},${plotsize}
set output "|/home/git/perfbook/utilities/gnuplotepsfix > timeskewhist.eps"
n=100
max=$max
min=$min
width=(max-min)/n
hist(x,width)=width*floor(x/width)+width/2.0
set boxwidth width*0.9
set style fill solid 0.5
set xlabel "Nanoseconds Deviation"
set ylabel "Frequency"
unset key

__EOF__
echo 'plot "'$T/wc-mono.dat'" u (hist($1,width)):(1.0) smooth freq w boxes lc rgb"grey" notitle' >> $T/hist.gnuplot

gnuplot $T/hist.gnuplot
