#!/bin/bash

prefix=$1
suffix=${2-.txt}

for i in 1 2 3 4 5 6 7 10 13 15 20
do
	sed -e 's/^\[.*\] //' -e '/---/d' < ${prefix}${i}${suffix} |
	head -n -1 |
	awk '
	BEGIN	{
		ordinal='$i'
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
done

