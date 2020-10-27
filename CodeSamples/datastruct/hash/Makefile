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
# Copyright (c) 2013-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

include ../../Makefile.arch

PROGS =	hash_bkt hash_bkt_hazptr hash_bkt_qsbr hash_bkt_rcu hash_global hash_resize hash_resize_s hash_unsync
LIB = ../../lib

top := ../..
include $(top)/depends.mk

ifeq ($(strip $(target)),)
all:
	@echo "### None in datastruct/hash/ can be built on arch: '$(arch)'."
else
all: $(PROGS)
endif

include $(top)/recipes.mk

hash_bkt: hash_bkt.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -o hash_bkt hash_bkt.c $(LIB)/random.c -lpthread

hash_bkt_ref: hash_bkt_ref.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -o hash_bkt_ref hash_bkt_ref.c $(LIB)/random.c -lpthread

hash_bkt_qsbr: hash_bkt_rcu.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -DPERFBOOK_RCU_QSBR -o hash_bkt_qsbr hash_bkt_rcu.c $(LIB)/random.c -lpthread -lurcu -lurcu-qsbr

hash_bkt_rcu: hash_bkt_rcu.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -o hash_bkt_rcu hash_bkt_rcu.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal

hash_bkt_hazptr: hash_bkt_hazptr.c ../../defer/hazptr.c ../../defer/hazptr.h ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -o hash_bkt_hazptr hash_bkt_hazptr.c ../../defer/hazptr.c $(LIB)/random.c -lpthread

hash_global: hash_global.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -o hash_global hash_global.c $(LIB)/random.c -lpthread

hash_resize: hash_resize.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -o hash_resize hash_resize.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal

hash_resize_s: hash_resize_s.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -o hash_resize_s hash_resize_s.c $(LIB)/random.c -lpthread -lurcu -lurcu-signal

hash_unsync: hash_unsync.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -DTEST_HASH -o hash_unsync hash_unsync.c $(LIB)/random.c -lpthread

clean:
	rm -f $(PROGS)
