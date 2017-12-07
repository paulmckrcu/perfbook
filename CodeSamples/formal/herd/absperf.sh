#!/bin/sh

TIMECMD=/usr/bin/time
TESTBASE=${1:-litmus-tests}
TIMEOUT=${2:-15m}
ITER=${3:-10}

for n in $(seq $ITER)
do
	for i in $TESTBASE/absperf/*.litmus
	do
		echo $i
		$TIMECMD timeout $TIMEOUT herd7 -conf linux-kernel.cfg $i
	done
done
