#!/bin/sh

ordinal=${1-}
sed -e 's/^\[.*\] //' -e '/---/d' |
head -n -1 |
awk '
BEGIN	{
	ordinal='$ordinal'
	}

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
	nsavg = nssum / ncs
	print ordinal, nsavg, sqrt(nssumsq/ncs - nsavg * nsavg)
	}'
