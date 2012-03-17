#!/bin/bash
#
# Generate a maze and solve with all solvers
#
# Usage: bash mazecmp.bash rows cols prefix [results]
#
#	rows: number of rows
#	cols: number of columns
#	prefix: path prefix for mazes, .fig, .png, -soln.png, and raw
#		maze binary files created
#	results: directory in which to accumulate results -- if not specified,
#		the script pops up a spreadsheet instead.

flavors="_seq _fg _part _2seq _seq_O3 _fg_O3 _part_O3 _2seq_O3 _seqP_O3 _fgP_O3 _partP_O3 _2seqP_O3 _seqC_O3 _fgC_O3 _partC_O3 _2seqC_O3"

rows=$1
cols=$2
prefix=$3
results=$4
if test -z "$rows" -o -z "$cols" -o -z "$prefix"
then
	echo usage ./mazecmp.bash rows cols path-prefix [ results ]
	exit 1
fi

# Generate the maze
echo ./maze_seq_O3 --generate $rows $cols --start -2 -2 --nofig --nosolve --output $prefix
time ./maze_seq_O3 --generate $rows $cols --start -2 -2 --nofig --nosolve --output $prefix

# Solve the maze with each solver.  Output .fig only for small mazes.
nofig=" --nofig"
if test "$rows" -le 200 -a "$cols" -le 200
then
	nofig=
fi
for i in $flavors
do
	echo "./maze${i} --input $prefix ${nofig} > ${prefix}${i}.fig"
	./maze${i} --input $prefix ${nofig} > ${prefix}${i}.fig 2> ${prefix}${i}.out
	cat ${prefix}${i}.out
done

# Compute the times and percentages.
seq_ms=`cat ${prefix}_seq.out | awk '{ print $6 }'`
seq_pct=`cat ${prefix}_seq.out | sed -e 's/^.*(//' -e 's/%)//'`
fg_ms=`cat ${prefix}_fg.out | awk '{ print $6 }'`
fg_pct=`cat ${prefix}_fg.out | sed -e 's/^.*(//' -e 's/%)//'`
part_ms=`cat ${prefix}_part.out | awk '{ print $6 }'`
part_pct=`cat ${prefix}_part.out | sed -e 's/^.*(//' -e 's/%)//'`
seq_O3_ms=`cat ${prefix}_seq_O3.out | awk '{ print $6 }'`
seq_O3_pct=`cat ${prefix}_seq_O3.out | sed -e 's/^.*(//' -e 's/%)//'`
fg_O3_ms=`cat ${prefix}_fg_O3.out | awk '{ print $6 }'`
fg_O3_pct=`cat ${prefix}_fg_O3.out | sed -e 's/^.*(//' -e 's/%)//'`
part_O3_ms=`cat ${prefix}_part_O3.out | awk '{ print $6 }'`
part_O3_pct=`cat ${prefix}_part_O3.out | sed -e 's/^.*(//' -e 's/%)//'`

if test -n "$results"
then
	# Accumulate results, if given a directory to accumulate them in.
	for i in ${flavors}
	do
		f=${results}/ms${i}
		touch $f
		cat ${prefix}${i}.out | awk '{ print $6 }' >> $f
		f=${results}/pct${i}
		touch $f
		cat ${prefix}${i}.out | sed -e 's/^.*(//' -e 's/%)//' >> $f
	done
	echo "seq_ms: $seq_ms fg_ms: $fg_ms part_ms: $part_ms"
	echo "seq_O3_ms: $seq_O3_ms fg_O3_ms: $fg_O3_ms part_O3_ms: $part_O3_ms"
	f=${results}/ms_seqVfg
	touch $f
	awk 'BEGIN { print '"$seq_ms"' / '"$fg_ms"' }' >> $f
	f=${results}/ms_seqVpart
	touch $f
	awk 'BEGIN { print '"$seq_ms"' / '"$part_ms"' }' >> $f
	f=${results}/ms_seqVseq_O3
	touch $f
	awk 'BEGIN { print '"$seq_ms"' / '"$seq_O3_ms"' }' >> $f
	f=${results}/ms_seq_O3Vfg_O3
	touch $f
	awk 'BEGIN { print '"$seq_O3_ms"' / '"$fg_O3_ms"' }' >> $f
	f=${results}/ms_seq_O3Vpart_O3
	touch $f
	awk 'BEGIN { print '"$seq_O3_ms"' / '"$part_O3_ms"' }' >> $f
	f=${results}/pct_seq_O3Vfg_O3
	touch $f
	awk 'BEGIN { print '"$seq_O3_pct"' / '"$fg_O3_pct"' }' >> $f
	f=${results}/pct_seq_O3Vpart_O3
	touch $f
	awk 'BEGIN { print '"$seq_O3_pct"' / '"$part_O3_pct"' }' >> $f
else
	# Create a spreadsheet and pop it up.
	echo '"seq ms","seq %","fg ms","fg %","fg speedup","part ms","part %","part speedup"' > $prefix.csv
	echo "$seq_ms,$seq_pct,$fg_ms,$fg_pct,=A2/C2,$part_ms,$part_pct,=A2/F2" >> $prefix.csv
	echo "$seq_O3_ms,$seq_O3_pct,$fg_O3_ms,$fg_O3_pct,=A3/C3,$part_O3_ms,$part_O3_pct,=A3/F3" >> $prefix.csv
	echo "=A2/A3,,=C2/C3,,=A2/C3,=F2/F3,,=A2/F3" >> $prefix.csv
	localc $prefix.csv
fi
