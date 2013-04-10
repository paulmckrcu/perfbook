#!/bin/bash
#
# Runs hash-table performance tests.
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

nsamples=17

for hash in hash_bkt hash_bkt_hazptr hash_bkt_rcu hash_global # hash_resize
do

	# Simple hash tables.
	for ncpu in 1 2 4 6 8 12 16 24 32 40 48 56 63
	do
		for ((i = 0; i < $nsamples; i++))
		do
			echo $hash --perftest --nreaders $ncpu --duration 1000 --updatewait 0
			./$hash --perftest --nreaders $ncpu --duration 1000 --updatewait 0
			sleep 1
		done
	done

	# Schroedinger hash tables, read-only.
	for ncpu in 1 2 4 6 8 12 16 24 32 40 48 56 63
	do
		for ((i = 0; i < $nsamples; i++))
		do
			echo $hash --schroedinger --nreaders $ncpu --duration 1000 --updatewait 0
			./$hash --schroedinger --nreaders $ncpu --duration 1000 --updatewait 0
			sleep 1
		done
	done

	# Schroedinger hash tables, read-only, with cats.
	for ncpu in 1 2 4 6 8 12 16 24 32 40 48 56 63
	do
		for ((i = 0; i < $nsamples; i++))
		do
			echo $hash --schroedinger --nreaders 63 --ncats $ncpu --duration 1000 --updatewait 0
			./$hash --schroedinger --nreaders 63 --ncats $ncpu --duration 1000 --updatewait 0
			sleep 1
		done
	done

	# Schroedinger hash tables, read-write, with cats.
	ncats=16
	nupd=16
	nread=32
	for ((i = 0; i < $nsamples; i++))
	do
		echo $hash --schroedinger --nreaders $nread --ncats $ncats --nupdaters $nupd --duration 1000 --updatewait 1
		./$hash --schroedinger --nreaders $nread --ncats $ncats --nupdaters $nupd --duration 1000 --updatewait 1
		sleep 1
	done
done
