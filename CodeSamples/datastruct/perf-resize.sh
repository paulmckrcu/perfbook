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
# Copyright (C) IBM Corporation, 2013
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

nsamples=7


# Simple hash tables, read-only.
for ncpu in 1 4 8 16 24 32 48 60
do
	for epw in 2048 16384 131072
	do
		for ((i = 0; i < $nsamples; i++))
		do
			echo hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets 1024 --elems/writer $epw --duration 1000 --updatewait 0
			./hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets 1024 --elems/writer $epw --duration 1000 --updatewait 0
			sleep 1
		done
		for ((i = 0; i < $nsamples; i++))
		do
			echo hash_resize --perftest --nreaders $ncpu --nbuckets 1024 --elems/writer $epw --resizemult 2 --duration 1000 --updatewait 0
			./hash_resize --perftest --nreaders $ncpu --nbuckets 1024 --elems/writer $epw --resizemult 2 --duration 1000 --updatewait 0
			sleep 1
		done
		for ((i = 0; i < $nsamples; i++))
		do
			echo hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets 2048 --elems/writer $epw --duration 1000 --updatewait 0
			./hash_bkt_rcu --perftest --nreaders $ncpu --nbuckets 2048 --elems/writer $epw --duration 1000 --updatewait 0
			sleep 1
		done
	done
done
