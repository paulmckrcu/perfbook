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
# Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

include ../../Makefile.arch

PROGS = existence_test \
	existence_3hash_test \
	existence_3hash_uperf \
	existence_3skiplist_test \
	existence_3skiplist_uperf \
	kaleidoscope_test \
	kaleidoscope_3hash_test \
	kaleidoscope_3skiplist_test \
	kaleidoscope_skiphash_test \
	procon_test
LIB = ../../lib

all: $(PROGS)

# NOTE:  For decent scalability on update-side tests as of early 2015,
#	 use something like jemalloc() instead of glibc malloc().
#	 If you install jemalloc at /home/paulmck/jemalloc, you will
#	 need the following additional arguments to cc:
#		-I/home/paulmck/jemalloc/include
#		-L/home/paulmck/jemalloc/lib
#		-Wl,--rpath,/home/paulmck/jemalloc/lib
#		-DUSE_JEMALLOC
#	 Verify by using the nm command and searching output for malloc.
#
#	So it is quite a bit easier to just use the default locations.  ;-)

existence_test: existence.h existence_test.c procon.h
	cc $(GCC_ARGS) -o existence_test existence_test.c -lpthread -lurcu -lurcu-signal

existence_3hash_test: existence.h hash_exists.h keyvalue.h existence_3hash_test.c procon.h
	cc $(GCC_ARGS) -o existence_3hash_test existence_3hash_test.c -lpthread -lurcu -lurcu-signal

existence_3hash_uperf: existence.h hash_exists.h keyvalue.h existence_3hash_uperf.c procon.h
	# cc -O0 -Wall -ggdb -fno-inline -o existence_3hash_uperf existence_3hash_uperf.c -ltcmalloc -lpthread -lurcu -lurcu-signal
	cc $(GCC_ARGS) -o existence_3hash_uperf existence_3hash_uperf.c -ltcmalloc -lpthread -lurcu -lurcu-signal

existence_3skiplist_test: existence.h skiplist_exists.h keyvalue.h existence_3skiplist_test.c procon.h
	cc -g -O0 -o existence_3skiplist_test existence_3skiplist_test.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal
	# cc $(GCC_ARGS) -o existence_3skiplist_test existence_3skiplist_test.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal

existence_3skiplist_uperf: existence.h hash_exists.h keyvalue.h existence_3skiplist_uperf.c procon.h
	# cc -O0 -Wall -ggdb -fno-inline -o existence_3skiplist_uperf existence_3skiplist_uperf.c -ltcmalloc $(LIB)/random.c -lpthread -lurcu -lurcu-signal
	cc $(GCC_ARGS) -o existence_3skiplist_uperf existence_3skiplist_uperf.c -ltcmalloc $(LIB)/random.c -lpthread -lurcu -lurcu-signal

kaleidoscope_test: kaleidoscope.h kaleidoscope_test.c procon.h
	cc $(GCC_ARGS) -o kaleidoscope_test kaleidoscope_test.c -lpthread -lurcu -lurcu-signal

kaleidoscope_3hash_test: kaleidoscope.h hash_exists.h keyvalue.h kaleidoscope_3hash_test.c procon.h
	cc $(GCC_ARGS) -o kaleidoscope_3hash_test kaleidoscope_3hash_test.c -lpthread -lurcu -lurcu-signal

kaleidoscope_3skiplist_test: kaleidoscope.h skiplist_exists.h keyvalue.h kaleidoscope_3skiplist_test.c procon.h
	cc -g -O0 -o kaleidoscope_3skiplist_test kaleidoscope_3skiplist_test.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal
	# cc $(GCC_ARGS) -o kaleidoscope_3skiplist_test kaleidoscope_3skiplist_test.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal

kaleidoscope_skiphash_test: kaleidoscope.h skiplist_exists.h keyvalue.h kaleidoscope_skiphash_test.c procon.h
	cc -g -O0 -o kaleidoscope_skiphash_test kaleidoscope_skiphash_test.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal
	# cc $(GCC_ARGS) -o kaleidoscope_skiphash_test kaleidoscope_skiphash_test.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal

procon_test: procon.h procon_test.c
	cc -O0 -g -o procon_test procon_test.c -lpthread -lurcu -lurcu-signal
	# cc $(GCC_ARGS) -o procon_test procon_test.c -lpthread -lurcu -lurcu-signal

clean:
	rm -f $(PROGS)
