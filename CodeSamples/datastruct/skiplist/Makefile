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
# Copyright (c) 2016 Paul E. McKenney, IBM Corporation.

include ../../Makefile.arch

PROGS =	skiplist

all: $(PROGS)

skiplist: skiplist.c ../../api.h skiplisttorture.h
	cc -O0 -g -o skiplist skiplist.c -lpthread -lurcu -lurcu-signal
	# cc $(GCC_ARGS) -o skiplist skiplist.c -lpthread -lurcu -lurcu-signal
	# cc $(GCC_ARGS) -o skiplist skiplist.c -lpthread -lurcu -lurcu-qsbr

clean:
	rm -f $(PROGS)
