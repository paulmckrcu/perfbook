#!/bin/sh

time=300
version=2.6.23
for ncpus in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
do

	dmesg -c > /dev/null
	insmod rcureadperf.ko nreaders=$ncpus test_duration=10
	sleep $time
	rmmod rcureadperf
	dmesg -c > ${version}-PREEMPT-DBG-r${ncpus}.txt
	sleep 10

	dmesg -c > /dev/null
	insmod rwlockreadperf.ko nreaders=$ncpus test_duration=10
	sleep $time
	rmmod rwlockreadperf
	dmesg -c > ${version}-PREEMPT-DBG-rwlr${ncpus}.txt
	sleep 10

	dmesg -c > /dev/null
	insmod atomicincperf.ko nreaders=$ncpus test_duration=10
	sleep $time
	rmmod atomicincperf
	dmesg -c > ${version}-PREEMPT-DBG-atomic_inc${ncpus}.txt
	sleep 10

done
