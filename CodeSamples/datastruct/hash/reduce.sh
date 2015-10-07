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
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright (C) IBM Corporation, 2013
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

tag="$1"

T=/tmp/reduce.sh.$$
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

# Produce .dat files for perftest
grep -e '--perftest' $T/sum |
awk -v tag="$tag" \
	'{
		dur = $9;
		print($14, $2 / dur) > "perftest." $11 "." tag ".dat"
	}'

# Produce .dat files for zoo scenario varying ncpus
grep -e '--schroedinger' $T/sum | grep -v -e '--nbuckets' |
grep -v -e '--nupdaters' | grep -v -e '--ncats' |
awk -v tag="$tag" \
	'{
		dur = $11;
		print($16, $2 / dur) > "zoo.cpus." $13 "." tag ".dat"
	}'
for i in 2048 4096 8192 16384
do
	grep -e '--schroedinger' $T/sum | grep -e "--nbuckets $i" |
	grep -v -e '--nupdaters' | grep -v -e '--ncats' |
	awk -v tag="$tag" -v i="$i" \
		'{
			dur = $11;
			print($16, $2 / dur) > "zoo.cpus." $13 "-" i "." tag ".dat"
		}'
done

# Produce .dat files for zoo scenario varying ncats.
grep -e '--ncats' $T/sum | grep -v -e '--nupdaters' |
awk -v tag="$tag" \
	'{
		dur = $11;
		print($18, $2 / dur) > "zoo.catall." $13 "." tag ".dat"
		print($18, $5 / dur) > "zoo.cat." $13 "." tag ".dat"
	}'

# Produce .dat files for zoo scenario varying updaters
grep -v -e '--ncats' $T/sum | grep -e '--nupdaters' |
awk -v tag="$tag" \
	'{
		dur = $11;
		print($18, " Reads: " $2 / dur " Readfails: " $3 / dur " Adds: " $7 / dur " Dels: " $9 / dur " (All in ms)") > "zoo.mix." $13 "." tag ".out"
		print($18, $2 / dur) > "zoo.updrd." $13 "." tag ".dat"
		print($18, ($7 + $9) / dur) > "zoo.upd." $13 "." tag ".dat"
	}'

# Produce .dat files for mixed zoo scenario.
sort -k18n $T/sum | grep -e '--ncats' | grep -e '--nupdaters' |
awk -v tag="$tag" \
	'{
		dur = $11;
		print($18, " Reads: " $2 / dur " Readfails: " $3 / dur " Catreads: " $5 / dur " Adds: " $7 / dur " Dels: " $9 / dur " (All in ms)") > "zoo.mix." $13 "." tag ".out"
		print($18, $2 / dur) > "zoo.reads." $13 "." tag ".dat"
		print($18, ($7 + $9) / dur) > "zoo.updates." $13 "." tag ".dat"
	}'

echo "Hit ^C to continue:"
sleep 10000
