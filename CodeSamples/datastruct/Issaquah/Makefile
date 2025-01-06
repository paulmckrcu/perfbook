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
# Copyright (c) 2015-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

include ../../Makefile.arch

PROGS = existence_test treetorture
LIB = ../../lib

top := ../..
include $(top)/depends.mk

ifeq ($(strip $(target)),)
all:
	@echo "### None in datastruct/Issaquah/ can be built on arch: '$(arch)'."
else
all: $(PROGS)
endif

include $(top)/recipes.mk

LURCU_SIG := $(shell pkg-config --libs liburcu-signal 2>/dev/null)

# NOTE:  For decent scalability on update-side tests as of early 2015,
#	 use something like jemalloc() instead of glibc malloc().
#	 If you install jemalloc at /home/paulmck/jemalloc, you will
#	 need the following additional arguments to cc:
#		-I/home/paulmck/jemalloc/include
#		-L/home/paulmck/jemalloc/lib
#		-Wl,--rpath,/home/paulmck/jemalloc/lib
#		-DUSE_JEMALLOC
#	 Verify by using the nm command and searching output for malloc.

existence_sub.o: existence.c existence.h ../../api.h
	cc $(GCC_ARGS) -o existence_sub.o -c -DSUBOBJ existence.c

existence_test: existence_sub.o existence_test.c ../../api.h
	cc $(GCC_ARGS) -o existence_test existence_sub.o existence_test.c -lpthread -lurcu $(LURCU_SIG)

spinlockmult_sub.o: spinlockmult.c spinlockmult.h ../../api.h
	cc $(GCC_ARGS) -o spinlockmult_sub.o -c -DSUBOBJ spinlockmult.c

treetorture: tree.c existence_sub.o spinlockmult_sub.o $(LIB)/random.c ../../api.h treetorture.h treetorturetrace.h $(LIB)/random.h existence.h tree.h
	cc $(GCC_ARGS) -o treetorture tree.c existence_sub.o spinlockmult_sub.o $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)

clean:
	rm -f $(PROGS)
