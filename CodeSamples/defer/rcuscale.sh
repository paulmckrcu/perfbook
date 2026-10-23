#!/bin/bash
#
# rcuscale.sh: Run a series of RCU, refcount, and rwlock scalability tests
#
# Usage: bash rcuscale.sh /path/to/Linux/repo
#
# On large systems, it may be necessary to adjust this script, for
# example, the taskset CPU list and the --cpus argument.
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

lkpath=${1}
if test -d "${lkpath}"
then
	:
else
	echo ${lkpath}: Not a directory, need Linux kernel source tree.
	exit 2
fi
set --

csdir="`pwd | sed -e 's,CodeSamples.*$,CodeSamples,'`"
. $csdir/functions.bash

cd $lkpath

if test -r kernel/rcu/refscale.c > /dev/null 2>&1
then
	:
else
	echo No 'refscale.c': Need recent Linux kernel source tree.
	exit 2
fi
if test -x tools/testing/selftests/rcutorture/bin/kvm-recheck-refscale*.sh > /dev/null 2>&1
then
	:
else
	echo No 'kvm-recheck-refscale*.c': Need recent Linux kernel source tree.
	exit 1
fi

T=/tmp/rcuscale.sh.$$
trap 'rm -f $T' 0 2

primlist="rcu rwlock refcnt"
if ((lastcpu > 100))
then
	holdoff=20
else
	holdoff=10
fi
if ((lastcpu * 2 >= maxcpu))
then
	holdoff=$((holdoff * 2))
fi

# Build.
tools/testing/selftests/rcutorture/bin/kvm.sh --allcpus --duration 10 --torture refscale --configs NOPREEMPT --kconfig "CONFIG_NR_CPUS=$((lastcpu + 1))" --trust-make --build-only > $T 2>&1
ret=$?
builddir="`grep -m 1 '^Results directory: ' $T | sed -e 's/^Results directory: *//'`"
if test "$ret" != 0
then
	echo "Build FAILED exit code $ret, results directory $T"
	exit 2
fi

incr=1
ncpus=1
maxtestcpu=$((lastcpu - 1)) # Leave two housekeeping CPUs
cpusperpwr2=4 # Coarser sampling than the default.
while test $ncpus -le $maxtestcpu
do
	endcpu=$((ncpus - 1))
	if test "$endcpu" -le 0
	then
		cpulist=0
	else
		cpulist=0-$endcpu
	fi
	for prim in $primlist
	do
		taskset -c $cpulist tools/testing/selftests/rcutorture/bin/kvm-again.sh "$builddir" --duration 10 --bootargs "refscale.scale_type=$prim refscale.nreaders=$ncpus refscale.loops=10000 refscale.holdoff=$holdoff" > $T 2>&1
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
		echo Run for $prim with $ncpus CPUs$fstr
		grep -E '^Points: | reader duration:' $T
	done
	incr=`power2inc $ncpus $cpusperpwr2 $maxtestcpu`
	ncpus=$((ncpus + incr))
done
