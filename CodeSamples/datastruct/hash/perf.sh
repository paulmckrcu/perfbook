#!/bin/bash
#
# Runs hash-table performance tests.  Note that resizing is tested
# by perf-resize.sh.
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

nsamples=30
smallncpus=64

csdir="`pwd | sed -e 's,CodeSamples.*$,CodeSamples,'`"
. $csdir/functions.bash
if test $smallncpus -gt $maxcpu
then
	smallncpus=$maxcpu
fi

nbuckets=$((lastcpu*5*100))
nbuckets=`power2up $nbuckets`
epw=$nbuckets

for ((i = 0; i < $nsamples; i++))
do
	for hash in hash_bkt hash_bkt_hazptr hash_bkt_qsbr hash_bkt_rcu hash_global hash_unsync
	do

		# Simple hash tables.
		ncpu=1
		while test $ncpu -le $lastcpu && (test $hash != hash_global || test $ncpu -le $smallncpus)
		do
			echo $hash --perftest --nreaders $ncpu --duration 1000 --updatewait 0 --nbuckets $nbuckets --elems/writer $epw '#' A
			./$hash --perftest --nreaders $ncpu --duration 1000 --updatewait 0 --nbuckets $nbuckets --elems/writer $epw
			sleep 0.1
			incr=`power2inc $ncpu $cpusperpwr2`
			ncpu=$((ncpu + incr))
		done

		# Schroedinger hash tables, read-only.
		ncpu=1
		while test $ncpu -le $lastcpu && (test $hash != hash_global || test $ncpu -le $smallncpus)
		do
			echo $hash --schroedinger --nreaders $ncpu --duration 1000 --updatewait 0 --nbuckets $nbuckets --elems/writer $epw '#' B
			./$hash --schroedinger --nreaders $ncpu --duration 1000 --updatewait 0 --nbuckets $nbuckets --elems/writer $epw
			sleep 0.1
			for bktmult in /4 /2 *1 *2 *4
			do
				bkts=$((nbuckets$bktmult))
				echo $hash --schroedinger --nreaders $ncpu --nbuckets $bkts --duration 1000 --updatewait 0 --elems/writer $epw '#' C
				./$hash --schroedinger --nreaders $ncpu --nbuckets $bkts --duration 1000 --updatewait 0 --elems/writer $epw
				sleep 0.1
			done
			incr=`power2inc $ncpu $cpusperpwr2`
			ncpu=$((ncpu + incr))
		done

		# Schroedinger hash tables, read-only, with cats.
		# Stick with a small number of CPUs to get meaningful
		# measurements for global locking and single-bucket
		# per-bucket locking.
		ncpu=1
		while test $ncpu -le $smallncpus
		do
			echo $hash --schroedinger --nreaders $smallncpus --ncats $ncpu --duration 1000 --updatewait 0 --nbuckets $nbuckets --elems/writer $epw '#' D
			./$hash --schroedinger --nreaders $smallncpus --ncats $ncpu --duration 1000 --updatewait 0 --nbuckets $nbuckets --elems/writer $epw
			sleep 0.1
			incr=`power2inc $ncpu $cpusperpwr2`
			ncpu=$((ncpu + incr))
		done

		# Schroedinger hash tables, read-write, no cats.
		nread=$((lastcpu-1))
		echo $hash --schroedinger --nreaders $nread --nupdaters 1 --duration 1000 --updatewait 0 --nbuckets $nbuckets --elems/writer $epw '#' E
		./$hash --schroedinger --nreaders $nread --nupdaters 1 --duration 1000 --updatewait 0 --nbuckets $nbuckets --elems/writer $epw
		sleep 0.1
		nupd=1
		while test $nupd -le $lastcpu && (test $hash != hash_global || test $nupd -le $smallncpus) && test $hash != hash_unsync
		do
			epwu=$((epw/nupd))
			if test $hash != hash_global
			then
				nread=$((lastcpu-nupd))
			else
				nread=$((smallncpus-nupd))
			fi
			echo $hash --schroedinger --nreaders $nread --nupdaters $nupd --duration 1000 --updatewait 1 --nbuckets $nbuckets --elems/writer $epwu '#' F
			./$hash --schroedinger --nreaders $nread --nupdaters $nupd --duration 1000 --updatewait 1 --nbuckets $nbuckets --elems/writer $epwu
			sleep 0.1
			incr=`power2inc $nupd $cpusperpwr2`
			nupd=$((nupd + incr))
		done

		if test $hash != hash_unsync
		then
			# Schroedinger hash tables, read-write, with cats.
			# Again, stick with a small number of CPUs to get
			# meaningful measurements for global locking and
			# single-bucket per-bucket locking.
			ncats=$((smallncpus/4))
			nupd=$((smallncpus/4))
			nread=$((smallncpus/2))
			echo $hash --schroedinger --nreaders $nread --ncats $ncats --nupdaters $nupd --duration 1000 --updatewait 1 --nbuckets $nbuckets --elems/writer $epw '#' G
			./$hash --schroedinger --nreaders $nread --ncats $ncats --nupdaters $nupd --duration 1000 --updatewait 1 --nbuckets $nbuckets --elems/writer $epw
			sleep 0.1
		fi

		# Schroedinger hash tables varying hash table size,
		# but maintaining constant occupancy.
		curepw=16
		maxepw=$((epw*32))
		while test $curepw -le $maxepw && test $hash != hash_global
		do
			echo $hash --schroedinger --nreaders $lastcpu --duration 1000 --updatewait 0 --nbuckets $curepw --elems/writer $curepw '#' H
			./$hash --schroedinger --nreaders $lastcpu --duration 1000 --updatewait 0 --nbuckets $curepw --elems/writer $curepw
			sleep 0.1
			incr=`power2inc $curepw 1`
			curepw=$((curepw + incr))
		done
	done
done
