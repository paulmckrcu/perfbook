#!/bin/bash
#
# Reduce hash-table performance data.
#
# Usage: sh reduce.sh tag
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
# Copyright (C) IBM Corporation, 2013
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

tag="$1"

T=/tmp/reduce.sh.$$
trap 'rm -rf $T' 0
mkdir $T

grep -v '^perf' | grep -v '^ns' | grep -v 'rcu_exit_sig:' > $T/filt
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

# Produce .dat files for perftest
grep -e '--perftest' $T/sum |
awk -v tag="$tag" \
	'{
		dur = $9;
		print($14, $2 / dur) > "perftest." $11 "." tag ".dat"
	}'

# Produce .dat files for zoo scenario varying ncpus
grep -e '--schroedinger' $T/sum |
grep -v -e '--nupdaters' | grep -v -e '--ncats' |
awk -v tag="$tag" \
	'{
		dur = $11;
		print($16, $2 / dur) > "zoo.cpus." $13 "." tag ".dat"
	}'

# Produce .dat files for zoo scenario varying ncats.
grep -e '--ncats' $T/sum | grep -v -e '--nupdaters' |
awk -v tag="$tag" \
	'{
		dur = $11;
		print($18, $2 / dur) > "zoo.cat." $13 "." tag ".dat"
		print($18, $5 / dur) > "zoo.catall." $13 "." tag ".dat"
	}'

# Produce .dat files for mixed zoo scenario.
grep -e '--ncats' $T/sum | grep -e '--nupdaters' |
awk -v tag="$tag" \
	'{
		dur = $11;
		print("Reads: " $2 / dur " Readfails: " $3 / dur " Catreads: " $5 / dur " Adds: " $7 / dur " Dels: " $9 / dur " (All in ms)") > "zoo.mix" $13 "." tag ".out"
	}'

echo "Hit ^C to continue:"
sleep 10000
