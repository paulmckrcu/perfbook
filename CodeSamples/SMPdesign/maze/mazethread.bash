#!/bin/bash
#
# Generate a square maze and solve with all solvers
#
# Usage: bash mazethread.sh rc nthreads prefix results
#
#	rc: number of rows and columns
#	nthreads: maximum number of threads
#	prefix: path prefix for mazes, .fig, .png, -soln.png, and raw
#		maze binary files created
#	results: directory in which to accumulate results

flavors="_fg_O3 _part_O3"

rc=$1
nthreads=$2
prefix=$3
results=$4
mkdir $results > /dev/null 2>&1 || :
if test -z "$rc" -o -z "$nthreads" -o -z "$prefix" -o -z "$results" -o ! -d "$results"
then
	echo usage ./mazethread.bash size nthreads path-prefix results
	exit 1
fi

# Generate the maze
echo ./maze_seq_O3 --generate $rc $rc --start -2 -2 --nofig --nosolve --output $prefix
time ./maze_seq_O3 --generate $rc $rc --start -2 -2 --nofig --nosolve --output $prefix

# Solve the maze with each solver.  Output .fig only for small mazes.
nofig=" --nofig"
if test "$rc" -le 200
then
	nofig=
fi

# Sequential for reference
for i in _seq_O3 _2seq_O3
do
	echo "./maze${i} --input $prefix ${nofig} > ${prefix}${i}.fig"
	./maze${i} --input $prefix ${nofig} > ${prefix}${i}.fig 2> ${prefix}${i}.out
	cat ${prefix}${i}.out
	# Accumulate results
	f=${results}/ms${i}
	touch $f
	cat ${prefix}${i}.out | awk '{ print $6 }' >> $f
	f=${results}/pct${i}
	touch $f
	cat ${prefix}${i}.out | sed -e 's/^.*(//' -e 's/%)//' >> $f
done

# Parallel for results
for i in $flavors
do
	if test "$i" = _part_O3
	then
		partargs="--threadstart diagonal"
	else
		partargs=""
	fi
	for ((j=1;j<=$nthreads;j++))
	do
		echo "./maze${i} --input $prefix --nthreads $j --threadstats ${nofig} ${partargs} > ${prefix}${i}-$j.fig"
		./maze${i} --input $prefix --nthreads $j --threadstats ${nofig} ${partargs} > ${prefix}${i}.fig 2> ${prefix}${i}-$j.out
		cat ${prefix}${i}-$j.out

		# Accumulate results
		f=${results}/ms${i}-$j
		touch $f
		tail -1 ${prefix}${i}-$j.out | awk '{ print $6 }' >> $f
		f=${results}/pct${i}-$j
		touch $f
		tail -1 ${prefix}${i}-$j.out | sed -e 's/^.*(//' -e 's/%)//' >> $f
	done
done
