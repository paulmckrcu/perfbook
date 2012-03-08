#!/bin/bash
#
# Make the specified number of attempts to create a maze of at least
# the specified quality.

n=$1
q=$2

T=/tmp/mazeq.sh.$$
trap 'rm -f $T' 0

for (( c=1; c<=$n; c++ ))
do
	./maze > /tmp/maze.fig 2> $T
	if grep -q '^Maze quality:' < $T
	then
		:
	else
		cp /tmp/maze.fig /tmp/badmaze.$c.fig
		fig2dev -L png -m 2 /tmp/maze.fig /tmp/badmaze.$c-V.png
		fig2dev -L png -m 2 -D +50 /tmp/maze.fig /tmp/badmaze.$c.png
		echo Unsolveable maze: 
	fi
	grep '^Maze quality:' < $T | awk '
	{
		print "echo Maze quality: " $3
		if ($3 >= '"$q"') {
			basename = "/tmp/maze-" $3
			name = basename ".fig"
			print "cp /tmp/maze.fig " name
			print "fig2dev -L png -m 2 " name " " basename "-S.png"
			print "fig2dev -L png -m 2 -D +50 " name " " basename ".png"
			print "echo Maze saved: " name
		}

	}' | sh
done
