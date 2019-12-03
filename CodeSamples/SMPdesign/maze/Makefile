# Makefile: build maze programs
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright (c) 2011-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

BINS = maze_seq maze_fg maze_part maze_2seq

all: $(BINS)

maze_seq: maze.h maze.c maze_seq.c
	cc -g -o maze_seq maze.c maze_seq.c -lrt
	cc -g -O3 -o maze_seq_O3 maze.c maze_seq.c -lrt
	cc -g -O3 -o maze_seqP_O3 -DCELL_PAD_SIZE=60 maze.c maze_seq.c -lrt
	cc -g -O3 -o maze_seqC_O3 -DCOLFIRST maze.c maze_seq.c -lrt

maze_fg: maze.h maze_parallel.h maze.c maze_fg.c
	cc -g -o maze_fg maze.c maze_fg.c -pthread -lrt
	cc -g -O3 -o maze_fg_O3 maze.c maze_fg.c -pthread -lrt
	cc -g -O3 -o maze_fgP_O3 -DCELL_PAD_SIZE=60 maze.c maze_fg.c -pthread -lrt
	cc -g -O3 -o maze_fgC_O3 -DCOLFIRST maze.c maze_fg.c -pthread -lrt

maze_part: maze.h maze_parallel.h maze.c maze_part.c
	cc -g -o maze_part maze.c maze_part.c -pthread -lrt
	cc -g -O3 -o maze_part_O3 maze.c maze_part.c -pthread -lrt
	cc -g -O3 -o maze_partP_O3 -DCELL_PAD_SIZE=60 maze.c maze_part.c -pthread -lrt
	cc -g -O3 -o maze_partC_O3 -DCOLFIRST maze.c maze_part.c -pthread -lrt

maze_2seq: maze.h maze_parallel.h maze.c maze_2seq.c
	cc -g -o maze_2seq maze.c maze_2seq.c -pthread -lrt
	cc -g -O3 -o maze_2seq_O3 maze.c maze_2seq.c -pthread -lrt
	cc -g -O3 -o maze_2seqP_O3 -DCELL_PAD_SIZE=60 maze.c maze_2seq.c -pthread -lrt
	cc -g -O3 -o maze_2seqC_O3 -DCOLFIRST maze.c maze_2seq.c -pthread -lrt

clean:
	rm -rf maze_seq maze_seq_O3 maze_seqP_O3 maze_seqC_O3
	rm -rf maze_fg maze_fg_O3 maze_fgP_O3 maze_fgC_O3
	rm -rf maze_part maze_part_O3 maze_partP_O3 maze_partC_O3
	rm -rf maze_2seq maze_2seq_O3 maze_2seqP_O3 maze_2seqC_O3
	rm -f gmon.out
