#!/bin/bash
#
# Generate a maze with and without solution.
#
# Usage: bash mazegen.sh mult prefix
#
#	mult: integral multiplier against default 41x32 maze (US Letter)
#	prefix: path prefix for mazes, .fig, .png, -soln.png, and raw
#		maze binary files created

mult=$1
prefix=$2

r=$(($mult*41))
c=$(($mult*32))
./maze_seq --generate $r $c --start -2 -2 --nofig --output $prefix
./maze_seq --input $prefix > ${prefix}.fig
fig2dev -L png -m2 ${prefix}.fig ${prefix}-soln.png
fig2dev -L png -m2 -D +50 ${prefix}.fig ${prefix}.png
