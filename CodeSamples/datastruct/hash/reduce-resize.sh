#!/bin/bash
#
# Reduce resizable hash-table performance data.
#
# Usage: sh reduce-resize.sh tag
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
# Copyright (C) IBM Corporation, 2013-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

tag="$1"

T=/tmp/reduce-resize.sh.$$
trap 'rm -rf $T' 0
mkdir $T

grep -v '^nohup:' | grep -v '^perf' | grep -v '^ns' | grep -v 'rcu_exit_sig:' > $T/filt
awk < $T/filt '
/^nlookups:/ {
		for (i = 1; i <= NF; i++) {
			if ($i ~ /[0-9][0-9]*/)
				l[old][i] += $i;
			else
				l[old][i] = $i;
		}
	}

/^hash/ {
		old = $0;
		sig[$0] = 1;
	}

END	{
		for (old in sig) {
			n = 0;
			for (i in l[old])
				n++;
			for (i = 1; i <= n; i++)
				printf "%s", l[old][i] " ";
			print "@@@ " old;
		}
	}' > $T/sum

# Find little and big numbers of buckets
nb="`grep -e --nbuckets $T/sum |
	sed -e 's/^.*--nbuckets //' | sed -e 's/ .*$//' | sort -u -k1n`"
nbs="`echo $nb | awk '{ print $1 }'`"
nbl="`echo $nb | awk '{ print $2 }'`"

# Produce .dat files for small fixed-size hash-table runs
ggrep -e '# S$' $T/sum |
awk -v tag="$tag" -v T=$T \
	'{
		dur = $9;
		print($14, $2 / dur) > T "/perftestS." $18 "." tag ".dat"
	}'

# Produce .dat files for resizable hash-table runs
grep -e '# R$' $T/sum |
awk -v tag="$tag" -v T=$T \
	'{
		dur = $9;
		print($14, $2 / dur) > T "/perftestR." $18 "." tag ".dat"
	}'

# Produce .dat files for large fixed-size hash-table runs
grep -e '# L$' $T/sum |
awk -v tag="$tag" -v T=$T \
	'{
		dur = $9;
		print($14, $2 / dur) > T "/perftestL." $18 "." tag ".dat"
	}'

# Produce .dat files for large fixed-size large-buckets hash-table runs
grep -e '# LL$' $T/sum |
awk -v tag="$tag" -v T=$T \
	'{
		dur = $9;
		print($14, $2 / dur) > T "/perftestLL." $18 "." tag ".dat"
	}'

datfiles="`cd $T; ls perftest*.dat`"
for i in $datfiles
do
	sort -k1n $T/$i > $i
done

echo "Hit ^C to continue:"
sleep 10000
