#!/bin/sh
#
# Create a maze appropriate for a patient and persistent human solver.
#
# Usage: sh makehumanmaze.sh [ basename [ quality [ <maze args> ] ] ]

basename=${1-/tmp/maze}
quality=${2-2}
shift
shift
mazeargs="${@}"
if test "${mazeargs}" = ""
then
	mazeargs="--generate 70 50"
fi

T="`mktemp ${TMPDIR-/tmp}/makehumanmaze.sh.XXXXXX`"
trap 'rm -rf $T' 0

n=1
maxq=0
while :
do
	./maze_part ${mazeargs} > ${basename}.fig 2> ${T}
	curq="`grep '^Maze quality:' ${T} |
		sed -e 's/(\([0-9.%]*\))/\1/' |
		awk '{ print $3 * $10 / 100.; }'`"
	d="`echo "${quality}" "${curq}" | awk '{ print ($2 >= $1); }'`"
	maxq="`echo "${curq}" "${maxq}" | awk '{ if ($1 > $2) print $1; else print $2; }'`"
	echo Attempt ${n}: `cat ${T}`: quality = ${curq} vs. ${quality}, max = ${maxq}
	if test "${d}" = 1
	then
		fig2dev -L pdf -m 2 -D +50 ${basename}.fig ${basename}.pdf
		fig2dev -L pdf -m 2 ${basename}.fig ${basename}-soln.pdf
		echo Maze: ${basename}.pdf  Solution: ${basename}-soln.pdf
		exit 0
	fi
	n="`expr ${n} + 1`"
done
