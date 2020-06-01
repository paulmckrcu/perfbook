#!/bin/bash
#
# rcudelay.sh: Run a series of RCU, refcount, and rwlock reader-delay tests
#
# Usage: bash rcudelay.sh [ lastdelay [ ncpus [ ncpus ... ] ] ]
#
# Run this in a recent Linux-kernel source tree.  On large systems,
# it may be necessary to adjust this script, for example, the
# taskset CPU list and the --cpus argument.  (If for no other reason
# than kernel build times can be very long when restricted to a
# single CPU.)
#
# Note: "lastdelay" is in nanoseconds.  The script starts at 100ns
# and steps logarithmically, as in 100, 200, 500, 1000, ...
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
# Copyright (c) 2020 Paul E. McKenney, Facebook.

if test -r kernel/rcu/refperf*.c > /dev/null 2>&1
then
	:
else
	echo No 'rcuperf*.c': Need recent Linux kernel source tree.
	exit 1
fi
if test -x tools/testing/selftests/rcutorture/bin/kvm-recheck-refperf*.sh > /dev/null 2>&1
then
	:
else
	echo No 'kvm-recheck-rcuperf*.c': Need recent Linux kernel source tree.
	exit 1
fi

T=/tmp/rcudelay.sh.$$
trap 'rm -f $T' 0 2

lastdelay=${1-30}
shift > /dev/null 2>&1
maxcpu="`grep '^processor' /proc/cpuinfo | tail -1 | awk '{ print $3 }'`"
if test -z "$1"
then
	cpus=$((maxcpu + 1))
else
	cpus=$*
fi
primlist="`grep '\.name[ 	]*=' kernel/rcu/refperf*.c |
	   sed -e 's/^[^"]*"//' -e 's/".*$//'`"

incr=1
for ncpus in $cpus
do
	if ((ncpus > 100))
	then
		holdoff=20
	else
		holdoff=10
	fi
	if ((ncpus * 2 >= maxcpu))
	then
		holdoff=$((holdoff * 2))
	fi
	endcpu=$((ncpus - 1))
	if test "$endcpu" -le 0
	then
		cpulist=0
	else
		cpulist=0-$endcpu
	fi
	curdelay=100
	while ((curdelay <= lastdelay))
	do
		for prim in $primlist
		do
			taskset -c $cpulist tools/testing/selftests/rcutorture/bin/kvm.sh --cpus $ncpus --duration 10 --torture refperf --configs NOPREEMPT --bootargs "refperf.perf_type=$prim refperf.nreaders=$ncpus refperf.loops=10000 refperf.holdoff=$holdoff refperf.readdelay=$curdelay" --kconfig "CONFIG_NR_CPUS=$((maxcpu + 1))" --trust-make > $T 2>&1
			ret=$?
			fstr=""
			resdir="`grep -m 1 '^Results directory: ' $T | sed -e 's/^Results directory: *//'`"
			if test "$ret" != 0
			then
				fstr=" FAILED $T"
			else
				if test -d "$resdir"
				then
					rm -rf "$resdir"
				fi
			fi
			echo Run for $prim with $ncpus CPUs and delay $curdelay$fstr
			egrep '^Points: | reader duration:' $T
		done
		curdelay=`echo $curdelay | sed -e 's/5/10/' -e t -e 's/2/5/' -e t -e 's/1/2/'`
	done
done
