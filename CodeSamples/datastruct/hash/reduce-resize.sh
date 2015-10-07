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
# Copyright (C) IBM Corporation, 2013
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

tag="$1"

T=/tmp/reduce-resize.sh.$$
trap 'rm -rf $T' 0
mkdir $T

grep -v '^nohup:' | grep -v '^perf' | grep -v '^ns' | grep -v 'rcu_exit_sig:' > $T/filt
awk < $T/filt '
/^nlookups:/ {
		for (i = 1; i <= NF; i++) {
			if ($i ~ /[0-9][0-9]*/)
				l[i] += $i;
			else
				l[i] = $i;
		}
	}

/^hash/ && $0 != old && old != "" {
		n = 0;
		for (i in l)
			n++;
		for (i = 1; i <= n; i++) {
			printf "%s", l[i] " ";
			l[i] = "";
		}
		print "@@@ " old;
		old = $0;
	}

/^hash/ && old == "" {
		old = $0;
	}

END	{
		n = 0;
		for (i in l)
			n++;
		for (i = 1; i <= n; i++) {
			printf "%s", l[i] " ";
			l[i] = "";
		}
		print "@@@ " old;
	}' > $T/sum

# Produce .dat files for small fixed-size hash-table runs
grep -v -e '--resizemult' $T/sum | grep -e '--nbuckets 1024' |
awk -v tag="$tag" \
	'{
		dur = $9;
		print($14, $2 / dur) > "perftestS." $18 "." tag ".dat"
	}'

# Produce .dat files for resizable hash-table runs
grep -e '--resizemult' $T/sum |
awk -v tag="$tag" \
	'{
		dur = $9;
		print($14, $2 / dur) > "perftestR." $18 "." tag ".dat"
	}'

# Produce .dat files for large fixed-size hash-table runs
grep -v -e '--resizemult' $T/sum | grep -e '--nbuckets 2048' |
awk -v tag="$tag" \
	'{
		dur = $9;
		print($14, $2 / dur) > "perftestL." $18 "." tag ".dat"
	}'

echo "Hit ^C to continue:"
sleep 10000
