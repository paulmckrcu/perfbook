#!/bin/bash
#
# Run cachetorture stats in a topology-aware manner.  First parameter
# controls the maximum CPU number, defaulting to the largest-numbered CPU.
# Second parameter gives the number of contiguous CPU numbers associated
# with a socket, defaulting to 28.

runtypes="atomicinc blindcmpxchg cmpxchg write"

maxcpu="`grep '^processor' /proc/cpuinfo | tail -1 | awk '{ print $3 }'`"
lastcpu=${1-$maxcpu}
socketrun=${2-28}

echo maxcpu: $maxcpu lastcpu: $lastcpu socketrun: $socketrun

for ((i=1;i<30;i++))
do
	for ((cpu0=0;cpu0<=$lastcpu;cpu0+=$socketrun))
	do
		for ((cpu1=$cpu0+1;cpu1<$cpu0+$socketrun;cpu1++))
		do
			for runtype in $runtypes
			do
				./cachetorture $runtype $cpu0 $cpu1
			done
		done
		for ((cpu1=$cpu0+$socketrun;cpu1<=$lastcpu;cpu1+=$socketrun))
		do
			for runtype in $runtypes
			do
				./cachetorture $runtype $cpu0 $cpu1
			done
		done
	done
done
