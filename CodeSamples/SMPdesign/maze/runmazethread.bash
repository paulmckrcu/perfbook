#!/bin/bash
#
# Generate lots of square mazes and solve with parallel solvers, recording
# statistics.
#
# Usage: bash runmazethread.bash nthreads results
#
#	nthreads: maximum number of threads to use
#	results: directory in which to accumulate results, in subdirectories
#		named after the maze size.

nthreads=$1
results=$2
mkdir $results > /dev/null 2>&1 || :
if test -z "$nthreads" -o -z "$results" -o ! -d "$results" -o ! -w "$results"
then
	echo usage ./runmazethread.sh nthreads results
	exit 1
fi

T=/tmp/runmazethread.sh.$$
trap 'rm -rf $T' 0
mkdir $T

for size in 20 50 100 200 500 1000 2000
do
	# Produce the mazes.
	mkdir $results/$size > /dev/null 2>&1 || :
	for ((i=0;i<100;i++))
	do
		./mazethread.bash $size $nthreads $T/maze $results/$size
	done
	
	# Reduce the data
	#(
	#	wd=`pwd`
	#	cd $results/$size
	#	bash $wd/plots.sh
	#)
done
