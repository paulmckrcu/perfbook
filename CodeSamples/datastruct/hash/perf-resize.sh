#!/bin/bash
#
# Runs resizable hash-table performance tests.
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
# Copyright (C) IBM Corporation, 2013-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

nsamples=30

csdir="`pwd | sed -e 's,CodeSamples.*$,CodeSamples,'`"
. $csdir/functions.bash

nbucketslo=$((lastcpu*5*100))
nbucketslo=`power2up $nbucketslo`
nbucketshi=$((nbucketslo*2))

# Simple hash tables, read-only.
for ((i = 0; i < $nsamples; i++))
do
	ncpu=1
	while test $ncpu -le $lastcpu
	do
		for epwmult in '' '*8'
		do
			epw=$((nbucketslo$epwmult))
			echo hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets $nbucketslo --elems/writer $epw --duration 1000 --updatewait 0 '#' S
			./hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets $nbucketslo --elems/writer $epw --duration 1000 --updatewait 0
			sleep 0.1

			# resizemult is 8/2, should compute...
			echo hash_resize --perftest --nreaders $ncpu --nbuckets $nbucketslo --elems/writer $epw --resizemult 4 --duration 1000 --updatewait 0 '#' R
			./hash_resize --perftest --nreaders $ncpu --nbuckets $nbucketslo --elems/writer $epw --resizemult 4 --duration 1000 --updatewait 0
			sleep 0.1

			echo hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets $nbucketshi --elems/writer $epw --duration 1000 --updatewait 0 '#' L
			./hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets $nbucketshi --elems/writer $epw --duration 1000 --updatewait 0
			sleep 0.1

		done

		echo hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets $epw --elems/writer $epw --duration 1000 --updatewait 0 '#' LL
		./hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets $epw --elems/writer $epw --duration 1000 --updatewait 0
		sleep 0.1

		incr=`power2inc $ncpu 8`
		ncpu=$((ncpu + incr))
	done
done
