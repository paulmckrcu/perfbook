#!/bin/bash
#
# Usage: findmeasrun.sh [ relpct ]
#
# This script reduces the data input, looking only at the first column,
# which is assumed to be numeric.  The underlying assumption is that each
# line is a measurement of a fixed quantity, and that bad measurements
# have large errors.  Therefore, the longest run of numbers having nearly
# the same value provides the maximum-likelihood estimate of that fixed
# quantity.
#
# The optional relpct argument (which defaults to 10 percent) gives an
# estimate of the relative error of good measurements of the fixed quantity.
#
# Output is in this format:
#	11:36 36% -> 5935:6511
#
# The "11" is the line number of the first measurement that was judged
# "good", and the "36" is the last such measurement.  The "36%" is the
# percentage of the total data that was judged "good".  The "5935" is
# the numeric value of the first good measurement, and finally the "6511"
# is the value of the last such measurement.
#
# Smaller values of relpct reject more data.  For example, relpct=5
# results in the following output:
#	17:25 25% -> 6109:6403
#
# Users of this script might take the first or last value, the median
# of the set of good values, the mean, or whatever statistic best fits
# the use case at hand.

relpct=${1-10}

awk -v relpct="${relpct}" '
{
	d[NR] = $1;
}

END {
	bestrunstart = runstart = 1;
	bestrunlength = runlength = 1;
	maxratio = 1.0 + relpct / 100.0;
	for (i = 2; i < NR; i++) {
		runlength++;
		denom = d[runstart];
		if (denom <= 0)
			denom = 1;
		while (i > runstart && d[i] / denom > maxratio) {
			runstart++;
			runlength--;
			denom = d[runstart];
			if (denom <= 0)
				denom = 1;
		}
		if (runlength > bestrunlength) {
			bestrunstart = runstart;
			bestrunlength = runlength;
		}
	}
	print bestrunstart ":" bestrunlength " " bestrunlength * 100.0 / NR "% -> " d[bestrunstart] ":" d[bestrunstart + bestrunlength - 1];
}'
