#!/bin/sh
#
# perf: run performance tests
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
# Copyright (c) 2014-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

tag=$1
if test -z "$tag"
then
	echo "Usage: sh perf.sh 2014.06.01a"
fi

touch lookup.$tag.txt data.$tag.txt data-moves.$tag.txt
for rep in 1 2 3 4 5 6 7
do
	for u in 1 2 4 8 16 32 60
	do
		echo ./treetorture --stresstest --nupdaters $u --one-to-one --every 2 --nel 4096 --affinity 1 --moveweight 0  --scanweight 0 --updateweight 0 >> lookup.$tag.txt
		./treetorture --stresstest --nupdaters $u --one-to-one --every 2 --nel 4096 --affinity 1 --moveweight 0  --scanweight 0 --updateweight 0 >> lookup.$tag.txt 2>&1
		echo ./treetorture --stresstest --nupdaters $u --one-to-one --every 2 --nel 4096 --affinity 1 >> data.$tag.txt
		./treetorture --stresstest --nupdaters $u --one-to-one --every 2 --nel 4096 --affinity 1 >> data.$tag.txt 2>&1
		echo ./treetorture --stresstest --nupdaters $u --one-to-one --every 2 --nel 4096 --lookupweight 0 --lookuprelaxweight 0 --moveweight 1 --scanweight 0 --updateweight 0 --affinity 1 >> data-moves.$tag.txt
		./treetorture --stresstest --nupdaters $u --one-to-one --every 2 --nel 4096 --lookupweight 0 --lookuprelaxweight 0 --moveweight 1 --scanweight 0 --updateweight 0 --affinity 1 >> data-moves.$tag.txt 2>&1
	done
done
