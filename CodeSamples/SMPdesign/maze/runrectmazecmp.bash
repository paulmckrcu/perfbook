#!/bin/bash
#
# Generate lots of rectangular mazes and solve with all solvers, recording
# statistics.
#
# Usage: bash runrectmazecmp.bash results
#
#	results: directory in which to accumulate results, in subdirectories
#		named after the maze size.

results=$1
mkdir $results > /dev/null 2>&1 || :
if test -z "$results" -o ! -d "$results" -o ! -w "$results"
then
	echo usage ./runrectmazecmp.sh results
	exit 1
fi

T=/tmp/runrectmazecmp.sh.$$
trap 'rm -rf $T' 0
mkdir $T

size=1000
cells=$(($size*$size))
for smallside in 1 5 10 20 50 100 200 500 1000
do
	# Produce the mazes.
	largeside=$(($cells/$smallside))
	fn=${largeside}x${smallside}
	mkdir $results/$fn > /dev/null 2>&1 || :
	for ((i=0;i<1000;i++))
	do
		./mazecmp.bash $largeside $smallside $T/maze $results/$fn
	done
done
