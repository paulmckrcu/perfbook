#!/bin/sh

sed -e 's/^\[.*\] //' -e '/---/d' |
head -n -1 |
awk '
	{
	scale = $5
	duration = $3
	csperunit = 0
	for (i = 7; i <= NF; i++) {
		csperunit += $i
		ns = 1000000000. / ($i * scale / duration)
		nssum += ns
		nssumsq += ns * ns
		ncs++
	}
	sum += csperunit
	sumsq += csperunit * csperunit
	}

END	{
	csps = sum * scale / NR / duration
	cspssq = sumsq * (scale / duration) * (scale / duration)
	nspcs = 1000000000./csps
	print "n=" NR " sum=" sum " duration=" duration " scale=" scale " CS/second=" csps " ns/CS=" nspcs
	print "csps: avg=" csps, " std=" sqrt(cspssq/NR - csps * csps)
	nsavg = nssum / ncs
	print "N=" ncs " nspcs: avg=" nsavg, " std=" sqrt(nssumsq/ncs - nsavg * nsavg)
	}'
