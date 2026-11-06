#!/bin/sh
#
# Usage: trimplot.sh [ arguments ... ] < {coe,fre,rfe}.dat
#	 trimplot.sh --help # List arguments and default values.
#
# This script trims noisy data from each end of a gnuplot single-value
# .dat file (each line containing only an x and a y value) by using the
# following procedure:
#
# 1.	Find the peak of the histogram (all values assumed positive).
# 2.	Find the most extreme buckets having at least --pctpeak times
#	this peak value, but using digital filtering, with new values
#	weighted --pctpeakfilt and the current estimate weighted (100 -
#	--pctpeakfilt).
# 3.	Take the delta between those two bucket values (the value
#	corresponding to the bucket, not the number of hits to those
#	buckets) and extend in both directions by --pctdelta times that
#	delta value.
# 4.	Take the resulting range, divide it by --divisor, then round
#	the result up to the next power of ten, double power of ten,
#	or quintuple power of ten, that is, the return value from
#	the round_up_125() function, when passed the range divided
#	by --divisor.
# 5.	Round the --pctdelta-extended ranges outwards by the result
#	returned by round_up_125().
#
# This script outputs a line containing the timestamp range, for example:
#	-2000 500
#
# These values can be converted to a gnuplot range: [-2000:500].
# Caution suggests plotting the full plot *and* the range, just to
# double-check this script's judgment on your particular data set.
#
# Specify --debug if you want to see intermediate results in the above
# calculation.  If set, this sets the "debugtp" awk variable that
# enables the debug print statements.
#
# This computation is of course empirical in nature.  We could also
# look at spacing between timestamps, looking for the minimum spacing,
# and finding the nearest larger gaps in both directions.  And we could
# adjust the default values of the parameters based on analysis of the data.
# Plus we could pick the peak, expand in both directions from there, pick
# the next peak, and so on, taking the union of the regions selected.
# Combinations of methods could of course be used.  But start simply!

# Parameter defaults
debugtp=0
divisor=5
pctdelta=10
pctpeak=10
pctpeakfilt=10

csdir="`pwd | sed -e 's,CodeSamples.*$,CodeSamples,'`"
. $csdir/functions.bash

scriptname="$0"

usage () {
	local debugdefault="disabled"

	if test "$debugtp" -ne 0
	then
		debugdefault="enabled"
	fi
	echo "Usage: $scriptname optional arguments:"
	echo "       --debug ($debugdefault)"
	echo "       --divisor full-range divisor ($divisor)"
	echo "       --pctdelta percent range extension ($pctdelta)"
	echo "       --pctpeak percent of peak cutoff ($pctpeak)"
	echo "       --pctpeakfilt percent weight for next data ($pctpeakfilt)"
	exit 1
}

while test $# -gt 0
do
	case "$1" in
	--debug)
		debugtp=1
		;;
	--divisor)
		checkarg --divisor "(divisor for timestamp range)" "$#" "$2" '^[0-9]*$' '^--'
		divisor=$2
		shift
		;;
	--pctdelta)
		checkarg --pctdelta "(percent extension for range)" "$#" "$2" '^[0-9]*$' '^--'
		pctdelta=$2
		shift
		;;
	--pctpeak)
		checkarg --pctpeak "(percent of peak exclusion)" "$#" "$2" '^[0-9]*$' '^--'
		pctpeak=$2
		shift
		;;
	--pctpeakfilt)
		checkarg --pctpeakfilt "(percent weight to next data point)" "$#" "$2" '^[0-9]*$' '^--'
		pctpeakfilt=$2
		shift
		;;
	"")
		# Ignore empty arguments.
		;;
	*)
		echo Unknown argument $1
		usage
		;;
	esac
	shift
done

awk -v pctpeak="$pctpeak" -v pctdelta="$pctdelta" -v divisor="$divisor" -v debugtp=$debugtp -v pctpeakfilt="$pctpeakfilt" '

# bucket_value(i) returns value at bucket adjusted for ts gaps on either
# side of that bucket.
function bucket_value(i,  curgap, nsides)
{
	curgap = 0.0;
	nsides = 0.0;

	# Gap below?
	if (i > 1) {
		curgap += ts[i] - ts[i - 1];
		nsides++;
	}

	# Gap above?
	if (i < NR) {
		curgap = ts[i + 1] - ts[i];
		nsides++;
	}

	return (pdf[i] * nsides) / curgap;
}

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
	ts[NR] = $1;
}
END {
	# Dump arguments if debugging.
	if (debugtp)
		print "debugtp = " debugtp " divisor = " divisor " pctdelta = " pctdelta " pctpeak = " pctpeak " pctpeakfilt = " pctpeakfilt;

	# We cannot do much with a single measurement, so just hand
	# it right back to them unaltered.
	if (NR == 1) {
		print ts[1], ts[1];
		exit 0;
	}

	# Find the peak based on bucket_value().
	peak = bucket_value(1);
	for (i = 2; i <= NR; i++) {
		curval = bucket_value(i);
		if (curval > peak)
			peak = curval;
	}

	# Find the smallest delta between consecutive timestamps.
	# This allows us to normalized variable-spaced data.
	mintsdelta = ts[NR] - ts[1];
	for (i = 2; i <= NR; i++) {
		curtsdelta = ts[i] - ts[i - 1];
		if (curtsdelta < mintsdelta)
			mintsdelta = curtsdelta;
	}
	if (debugtp)
		print "mintsdelta = " mintsdelta;

	# Compute the desired percentage of the peak bucket value.
	cutoff = peak * pctpeak / 100;
	if (debugtp)
		print "peak = " peak " pctpeak = " pctpeak " cutoff = " cutoff;

	# Find the most extreme buckets containing at least the cutoff
	# value (after digital filtering).
	curval = bucket_value(1);
	for (lownr = 2; curval < cutoff && lownr <= NR; lownr++) {
		curpoint = bucket_value(lownr);
		curval = (curpoint * pctpeakfilt + curval * (100 - pctpeakfilt)) / 100;
	}
	curval = bucket_value(NR);
	for (highnr = NR - 1; curval < cutoff && highnr >= 1; highnr--) {
		curpoint = bucket_value(highnr);
		curval = (curpoint * pctpeakfilt + curval * (100 - pctpeakfilt)) / 100;
	}
	if (debugtp)
		print "lownr = " lownr " highnr = " highnr;

	# Convert from buckets to the corresponding timestamp values.
	lowts = ts[lownr];
	hights = ts[highnr];
	if (debugtp)
		print "lowts = " lowts " hights = " hights;

	# Adjust the timestamp range out by pctdelta of that range,
	# then locate the corresponding buckets.
	deltats = (hights - lowts) * pctdelta / 100;
	if (debugtp)
		print "deltats = " deltats;
	lowdeltats = lowts - deltats;
	highdeltats = hights + deltats;
	if (debugtp)
		print "lowdeltats = " lowdeltats " highdeltats = " highdeltats;
	for (lowdeltanr = 1; ts[lowdeltanr] < lowdeltats; lowdeltanr++)
		continue;
	for (highdeltanr = NR; ts[highdeltanr] > highdeltats; highdeltanr--)
		continue;

	# Divide the expanded timestamp range by the divisor, then round
	# up to the next 1/2/5 multiple of a power of ten.
	rawrangets = (highdeltats - lowdeltats) / divisor;
	rangets125 = round_up_125(rawrangets);
	if (debugtp)
		print "rangets125 = " rangets125;

	# Round the (lowdeltats,highdeltats) range outwards by the
	# resulting rangets125 value.
	low125ts = roundby(lowdeltats, rangets125, 0);
	high125ts = roundby(highdeltats, rangets125, 1);
	if (debugtp)
		print "Before range check: low125ts = " low125ts " high125ts = " high125ts;

	# Bound the resulting (low125ts,high125ts) range by the timestamp
	# range in the input data.
	if (low125ts < ts[1])
		low125ts = ts[1];
	if (high125ts > ts[NR])
		high125ts = ts[NR];
	if (debugtp)
		print "After range check: low125ts = " low125ts " high125ts = " high125ts;

	# Accumulate statistics.
	for (i = 1; i <= NR; i++)
		if (ts[i] >= low125ts) {
			low125nr = i;
			break;
		}
	low125ignored = 0;
	for (i = 1; i < low125nr; i++)
		low125ignored += pdf[i];
	for (i = NR; i >= 1; i--)
		if (ts[i] <= high125ts) {
			high125nr = i;
			break;
		}
	high125ignored = 0;
	for (i = NR; i >= high125nr; i--)
		high125ignored += pdf[i];
	if (debugtp)
		print "NR = " NR " low125nr = " low125nr " high125nr = " high125nr " ts[1] = " ts[1] " ts[NR] = " ts[NR];

	# Print result and diagnostics.
	print low125ts, high125ts, "# Ignored: Buckets: " low125nr - 1 "+" NR - high125nr "=" NR - high125nr + low125nr - 1 " of " NR " Counts: " low125ignored "+" high125ignored "=" low125ignored + high125ignored " of " sum;
}'
