#!/bin/sh

time=300
version=2.6.23
ncpus=16
for csw in 1 2 5 7 10 13 15 20
do

	dmesg -c > /dev/null
	insmod rcureadperfwt.ko nreaders=$ncpus test_duration=10 critical_section_weight=$csw
	sleep $time
	rmmod rcureadperfwt
	dmesg -c > ${version}-PREEMPT-DBG-r16-wt${csw}.txt
	sleep 10

	dmesg -c > /dev/null
	insmod rwlockreadperfwt.ko nreaders=$ncpus test_duration=10 critical_section_weight=$csw
	sleep $time
	rmmod rwlockreadperfwt
	dmesg -c > ${version}-PREEMPT-DBG-rwlr16-wt${csw}.txt
	sleep 10

	dmesg -c > /dev/null
	insmod atomicrefperfwt.ko nreaders=$ncpus test_duration=10 critical_section_weight=$csw
	sleep $time
	rmmod atomicrefperfwt
	dmesg -c > ${version}-PREEMPT-DBG-atomic_inc16-wt${csw}.txt
	sleep 10

done
