#!/bin/sh

awk '
/absperf/ {
	curtest=$1;
	testran = 0;
}

/^Test/ {
	testran = 1;
}

/maxresident)k/ {
	if (testran) {
		curtesttime = $0;
		gsub(/user .*$/, "", curtesttime);
		testtime_n[curtest]++;
		testtime_sum[curtest] += curtesttime;
		if (testtime_max[curtest] == "" || curtesttime + 0 > testtime_max[curtest] + 0)
			testtime_max[curtest] = curtesttime;
		if (testtime_min[curtest] == "" || curtesttime + 0 < testtime_min[curtest] + 0)
			testtime_min[curtest] = curtesttime;
	}
}

END {
	for (i in testtime_n)
		print i, testtime_sum[i] / testtime_n[i], testtime_min[i], testtime_max[i];
}
'
