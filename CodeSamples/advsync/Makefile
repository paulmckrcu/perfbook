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
# Copyright (c) 2008 Paul E. McKenney, IBM Corporation.

include ../Makefile.arch

PROGS =	q singleq wfenqueue

all: $(PROGS)

top := ..
include $(top)/depends.mk

q: q.c q.h queuetorture.h ../api.h
	cc $(GCC_ARGS) -o q -DTEST q.c -lpthread

singleq: singleq.c singleq.h queuetorture.h ../api.h
	cc $(GCC_ARGS) -o singleq -DTEST singleq.c -lpthread

wfenqueue: wfenqueue.c q.h queuetorture.h ../api.h
	cc $(GCC_ARGS) -o wfenqueue -DTEST wfenqueue.c -lpthread

clean:
	rm -f $(PROGS)
