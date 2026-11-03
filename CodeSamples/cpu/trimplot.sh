#!/bin/sh
#
# Usage: trimplot.sh [ %peak [ %delta [ divisor ] ] ]
#
# Find the peak of the histogram (all values assumed positive).
# Find the most extreme buckets having at least %peak times this
#	peak value.
# Take the delta between those two bucket values (the value
#	corresponding to the bucket, not the number of hits to those
#	buckets, and extend in both directions by %delta times that
#	delta value.
# Take the resulting range, divide it by the divisor, then round the
#	result up to the next power of ten, double power of ten, or
#	quintuple power of ten, that is, the round_up_125() function.
# Round the %delta-extended ranges outwards by the result returned by
#	the round_up_125().
#
# This is of course empirical in nature.  If it fails, the %peak search
# could use digital filtering, which likely allows smaller values of %peak
# to decrease.  Combinations of methods could be used for the %peak
# search.  But start simply!

pctpeak=${1-10}
pctdelta=${2-10}
divisor=${3-5}

awk -v pctpeak="$pctpeak" -v pctdelta="$pctdelta" -v divisor="$divisor" '

# round_up_125(v) returns:
# 	v if exact power of ten, 
#	Next double power of ten if between,
#	Next quintuple power of ten if between,
#	Next power of ten otherwise.
#
# So, 10->10, 113->200, 3553->5000, and 65536->100000.
# Also, 2->2 and 50->50.
function round_up_125(v,  l, m, n)
{
	l = log(v) / log(10);
	if (int(l) == l) {
		m = v;
	} else {
		n = 10 ^ (int(l) + 1);
		if (n / 5 >= v)
			m = n / 5;
		else if (n / 2 >= v)
			m = n / 2;
		else
			m = n;
	}
	return m;
}

# roundby(v, r, roundup) returns v rounded to the next multiple of r
# in the negative direction if roundup==0 and in the positive direction
# otherwise.
function roundby(v, r, roundup,  vr)
{
	vr = int(v / r) * r;
	if (vr == v)
		return v;
	if (roundup && v > 0)
		return vr + r;
	else if (!roundup && v < 0)
		return vr - r;
	return vr;
}

BEGIN {
	sum = 0;
}

{
	sum += $2;
	pdf[NR] = $2;
	cdf[NR] = sum;
	ts[NR] = $1;
	if (peak < $2)
		peak = $2;
}
END {
	# Compute the desired percentage of the peak bucket value.
	cutoff = peak * pctpeak / 100;
	# print "cutoff = " cutoff; # @@@

	# Find the most extreme buckets containing at least the cutoff
	# value.
	for (lownr = 1; pdf[lownr] < cutoff; lownr++)
		continue;
	for (highnr = NR; pdf[highnr] < cutoff; highnr--)
		continue;

	# Find the corresponding timestamp values.
	lowts = ts[lownr];
	hights = ts[highnr];
	# print "lowts = " lowts " hights = " hights; # @@@

	# Adjust the timestamp range out by pctdelta of the span, then
	# find the corresponding buckets.
	deltats = (hights - lowts) * pctdelta / 100;
	# print "deltats = " deltats; # @@@
	lowdeltats = lowts - deltats;
	highdeltats = hights + deltats;
	# print "lowdeltats = " lowdeltats " highdeltats = " highdeltats; # @@@
	for (lowdeltanr = 1; ts[lowdeltanr] < lowdeltats; lowdeltanr++)
		continue;
	for (highdeltanr = NR; ts[highdeltanr] > highdeltats; highdeltanr--)
		continue;

	# Divide the expanded timestamp range by the divisor, then round
	# up to the next 1/2/5 multiple of a power of ten.
	rawrangets = (highdeltats - lowdeltats) / divisor;
	rangets125 = round_up_125(rawrangets);
	# print "rangets125 = " rangets125; # @@@

	# Round the (lowdeltats,highdeltats) outwards by the resulting
	# rangets125 value.
	low125ts = roundby(lowdeltats, rangets125, 0);
	high125ts = roundby(highdeltats, rangets125, 1);
	# print "low125ts = " low125ts " high125ts = " high125ts; # @@@

	# Dump the data that is in range.
	for (i = 1; i <= NR; i++)
		if (ts[i] >= low125ts && ts[i] <= high125ts)
			print ts[i], pdf[i];
}'
