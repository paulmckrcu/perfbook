# Utility functions for use with bash.
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
# Copyright (C) Facebook, 2020
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

# There are about five buckets per 64-byte cache line, and up to about
# 448 CPUs.  Giving each CPU its own cache line in a deterministic workload
# requires 448*5=2240 cache lines.  But in this case, there is a very high
# probability of cacheline collision.  Multiplying the number of buckets
# by 100 (22400) reduces the per-access chance of cacheline collision to
# roughly 1% (computing the exact value is left as an exercise).  Rounding
# to the next power of two gets 262,144.  So use this and 524,288.
#
# But use the actual maximum number of CPUs instead of hard-coding 448.
# Also round down because laziness.

# Power of two, rounding down and up, respectively.
power2down() {
	echo $1 |
	awk '
	{
		x = $1;
		logx = log(x) / log(2);
		ilogx = int(logx);
		print 2^ilogx;
	}'
}

power2up() {
	echo $1 |
	awk '
	{
		x = $1;
		logx = log(x) / log(2);
		ilogx = int(logx);
		if (x == 2^ilogx)
			print 2^ilogx;
		else
			print 2 * 2^ilogx;
	}'
}

# Iteration increment given last number used and divisor (which should
# be a power of two).  If the result would be fractional, it is rounded up
# to 1.  So "power2inc 64 1" will give 64 (one sample per power of two),
# and "power2inc 64 8" will give 8 (eight samples per power of two).
power2inc() {
	awk -v iter=$1 -v p2div=$2 -v p2raw="`power2down $1`" < /dev/null '
	BEGIN {
		if (p2raw <= p2div)
			print 1;
		else
			print p2raw / p2div;
	}'
}

# Get CPU numbers
maxcpu="`grep '^processor' /proc/cpuinfo | tail -1 | awk '{ print $3 }'`"
maxcpu=$((maxcpu + 1))
lastcpu=${1-$maxcpu}
if test $lastcpu -gt $maxcpu
then
	echo $0: Specified $lastcpu CPUs, only $maxcpu available!!!
	exit
fi
cpusperpwr2=8
