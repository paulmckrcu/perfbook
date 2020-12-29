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
# Copyright (C) IBM Corporation, 2013-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

tag="$1"

T=/tmp/reduce.sh.$$
trap 'rm -rf $T' 0 2
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
		sig[$0] = 1; # Signature of test will allow later collation
	}

END	{
		for (old in sig) {
			n = 0;
			if (!(old in l)) {
				print("Missing element: " old) > "/dev/stderr";
				continue;
			}
			for (i in l[old])
				n++;
			for (i = 1; i <= n; i++)
				printf "%s", l[old][i] " ";
			print "@@@ " old;
		}
	}' > $T/sum

# Produce .dat files for perftest
echo "# Produce .dat files for perftest" 1>&2
grep -e "# A$" $T/sum |
awk -v tag="$tag" -v T="$T" \
	'{
		dur = $9;
		print($14, $2 / dur) > T "/perftest." $11 "." tag ".dat"
	}'

# Produce .dat files for zoo scenario varying ncpus
echo '# Produce .dat files for zoo scenario varying ncpus' 1>&2
grep -e "# B$" $T/sum |
awk -v tag="$tag" -v T="$T" \
	'{
		dur = $11;
		print($16, $2 / dur) > T "/zoo.cpus." $13 "." tag ".dat"
	}'
echo '# Produce .dat files for zoo scenario varying hash size' 1>&2
nb="`grep -e "# C$" $T/sum | grep -e "--nbuckets" |
	sed -e 's/^.*--nbuckets //' | sed -e 's/ .*$//' | sort -u -k1n`"
for i in $nb
do
	grep -e "# C$" $T/sum | grep -e "--nbuckets $i" |
	awk -v tag="$tag" -v i="$i" -v T="$T" \
		'{
			dur = $11;
			print($16, $2 / dur) > T "/zoo.cpus." $13 "-" i "." tag ".dat"
		}'
done

# Produce .dat files for zoo scenario varying ncats.
echo '# Produce .dat files for zoo scenario varying ncats.' 1>&2
grep -e "# D$" $T/sum |
awk -v tag="$tag" -v T="$T" \
	'{
		dur = $11;
		print($18, $2 / dur) > T "/zoo.catall." $13 "." tag ".dat"
		print($18, $5 / dur) > T "/zoo.cat." $13 "." tag ".dat"
	}'

# Produce .dat files for zoo scenario varying updaters
echo '# Produce .dat files for zoo scenario varying updaters' 1>&2
grep -e "# F$" $T/sum |
awk -v tag="$tag" -v T="$T" \
	'{
		dur = $11;
		print($18, " Reads: " $2 / dur " Readfails: " $3 / dur " Adds: " $7 / dur " Dels: " $9 / dur " (All in ms)") > "zoo.mix." $13 "." tag ".out"
		print($18, $2 / dur) > T "/zoo.updrd." $13 "." tag ".dat"
		print($18, ($7 + $9) / dur) > T "/zoo.upd." $13 "." tag ".dat"
	}'

# Produce .dat files for mixed zoo scenario.
echo '# Produce .dat files for mixed zoo scenario.' 1>&2
grep -e "# G$" $T/sum |
awk -v tag="$tag" -v T="$T" \
	'{
		dur = $11;
		print($18, " Reads: " $2 / dur " Readfails: " $3 / dur " Catreads: " $5 / dur " Adds: " $7 / dur " Dels: " $9 / dur " (All in ms)") > "zoo.mix." $13 "." tag ".out"
		print($18, $2 / dur) > T "/zoo.reads." $13 "." tag ".dat"
		print($18, ($7 + $9) / dur) > T "/zoo.updates." $13 "." tag ".dat"
	}'

# Produce .dat files for zoo scenario varying hash-table size.
echo '# Produce .dat files for zoo scenario varying hash-table size.' 1>&2
grep -e "# H$" $T/sum |
awk -v tag="$tag" -v T="$T" \
	'{
		dur = $11;
		print($22, $2 / dur) > T "/zoo.hashsize." $13 "." tag ".dat"
	}'

datfiles="`cd $T; ls *.dat`"
for i in $datfiles
do
	sort -k1n $T/$i > $i
done

echo "Hit ^C to continue:"
sleep 10000
