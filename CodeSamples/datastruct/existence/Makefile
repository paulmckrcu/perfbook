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

LURCU_SIG := $(shell pkg-config --libs liburcu-signal 2>/dev/null)

all: $(PROGS)

# NOTE:  The two *_uperf tests need a scalable allocator: they allocate and
#	 free an existence group, and the keys and elements it commits, on
#	 every rotation on every updater thread, so glibc malloc's arena
#	 contention limits them well before the technique under test does.
#	 These targets therefore link against jemalloc when it is installed,
#	 and define USE_JEMALLOC, which selects per-CPU arenas (see the
#	 comment on malloc_conf in existence_3hash_uperf.c).
#
#	 If jemalloc is not installed, they fall back to glibc malloc, which
#	 builds and runs but does not scale on the update side.  Override
#	 MALLOC to pick another allocator, or to force the fallback:
#
#		make MALLOC=-ltcmalloc	# what these targets used to hardcode
#		make MALLOC=		# glibc malloc
#
#	 Verify by using the nm or ldd command and searching output for malloc.
MALLOC ?= $(shell pkg-config --libs jemalloc 2>/dev/null)
MALLOC_CFLAGS = $(if $(findstring jemalloc,$(MALLOC)),-DUSE_JEMALLOC)
ifeq ($(strip $(MALLOC)),)
MALLOC_NOTE = @echo 'NOTE: no jemalloc, using glibc malloc: this will not scale.'
endif

existence_test: existence.h existence_test.c procon.h
	cc $(GCC_ARGS) -o existence_test existence_test.c -lpthread -lurcu $(LURCU_SIG)

existence_3hash_test: existence.h hash_exists.h keyvalue.h existence_3hash_test.c procon.h
	cc $(GCC_ARGS) -o existence_3hash_test existence_3hash_test.c -lpthread -lurcu $(LURCU_SIG)

existence_3hash_uperf: existence.h hash_exists.h keyvalue.h existence_3hash_uperf.c procon.h
	# cc -O0 -Wall -ggdb -fno-inline $(MALLOC_CFLAGS) -o existence_3hash_uperf existence_3hash_uperf.c $(MALLOC) -lpthread -lurcu $(LURCU_SIG)
	$(MALLOC_NOTE)
	cc $(GCC_ARGS) $(MALLOC_CFLAGS) -o existence_3hash_uperf existence_3hash_uperf.c $(MALLOC) -lpthread -lurcu $(LURCU_SIG)

existence_3skiplist_test: existence.h skiplist_exists.h keyvalue.h existence_3skiplist_test.c procon.h
	cc -g -O0 -o existence_3skiplist_test existence_3skiplist_test.c $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)
	# cc $(GCC_ARGS) -o existence_3skiplist_test existence_3skiplist_test.c $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)

existence_3skiplist_uperf: existence.h hash_exists.h keyvalue.h existence_3skiplist_uperf.c procon.h
	# cc -O0 -Wall -ggdb -fno-inline $(MALLOC_CFLAGS) -o existence_3skiplist_uperf existence_3skiplist_uperf.c $(MALLOC) $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)
	$(MALLOC_NOTE)
	cc $(GCC_ARGS) $(MALLOC_CFLAGS) -o existence_3skiplist_uperf existence_3skiplist_uperf.c $(MALLOC) $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)

kaleidoscope_test: kaleidoscope.h kaleidoscope_test.c procon.h
	cc $(GCC_ARGS) -o kaleidoscope_test kaleidoscope_test.c -lpthread -lurcu $(LURCU_SIG)

kaleidoscope_3hash_test: kaleidoscope.h hash_exists.h keyvalue.h kaleidoscope_3hash_test.c procon.h
	cc $(GCC_ARGS) -o kaleidoscope_3hash_test kaleidoscope_3hash_test.c -lpthread -lurcu $(LURCU_SIG)

kaleidoscope_3skiplist_test: kaleidoscope.h skiplist_exists.h keyvalue.h kaleidoscope_3skiplist_test.c procon.h
	cc -g -O0 -o kaleidoscope_3skiplist_test kaleidoscope_3skiplist_test.c $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)
	# cc $(GCC_ARGS) -o kaleidoscope_3skiplist_test kaleidoscope_3skiplist_test.c $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)

kaleidoscope_skiphash_test: kaleidoscope.h skiplist_exists.h keyvalue.h kaleidoscope_skiphash_test.c procon.h
	cc -g -O0 -o kaleidoscope_skiphash_test kaleidoscope_skiphash_test.c $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)
	# cc $(GCC_ARGS) -o kaleidoscope_skiphash_test kaleidoscope_skiphash_test.c $(LIB)/random.c -lpthread -lurcu $(LURCU_SIG)

procon_test: procon.h procon_test.c
	cc -O0 -g -o procon_test procon_test.c -lpthread -lurcu $(LURCU_SIG)
	# cc $(GCC_ARGS) -o procon_test procon_test.c -lpthread -lurcu $(LURCU_SIG)

clean:
	rm -f $(PROGS)
