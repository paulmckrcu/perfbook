#!/bin/bash
#
# Generate lots of square mazes and solve with all solvers, recording
# statistics.
#
# Usage: bash runmazecmp.bash results
#
#	results: directory in which to accumulate results, in subdirectories
#		named after the maze size.

results=$1
mkdir $results > /dev/null 2>&1 || :
if test -z "$results" -o ! -d "$results" -o ! -w "$results"
then
	echo usage ./runmazecmp.sh results
	exit 1
fi

T=/tmp/runmazecmp.sh.$$
trap 'rm -rf $T' 0
mkdir $T

for size in 20 50 100 200 500 1000
do
	# Produce the mazes.
	mkdir $results/$size > /dev/null 2>&1 || :
	for ((i=0;i<500;i++))
	do
		./mazecmp.bash $size $size $T/maze $results/$size
	done
	
	# Reduce the data
	# (
	# 	wd=`pwd`
	# 	cd $results/$size
	# 	bash $wd/plots.sh
	# )
done
