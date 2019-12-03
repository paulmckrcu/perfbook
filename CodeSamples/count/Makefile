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
# Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

include ../Makefile.arch

PROGS =	count_atomic \
	count_end \
	count_end_rcu \
	count_lim \
	count_lim_app \
	count_lim_atomic \
	count_lim_sig \
	count_limd \
	count_nonatomic \
	count_stack \
	count_stat \
	count_stat_atomic \
	count_stat_eventual \
	count_tstat

RCU_SRCS = ../defer/rcu_nest32.h ../defer/rcu_nest32.c

top := ..
include $(top)/depends.mk

ifeq ($(strip $(target)),)
all:
	@echo "### None in count/ can be built on arch: '$(arch)'."
else
all: $(PROGS)
endif

CC?=cc

include $(top)/recipes.mk

count_atomic: count_atomic.c ../api.h counttorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_atomic count_atomic.c -lpthread

count_end: count_end.c ../api.h counttorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_end count_end.c -lpthread

count_end_rcu: count_end_rcu.c ../api.h counttorture.h $(RCU_SRCS)
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_end_rcu count_end_rcu.c -lpthread

count_lim: count_lim.c ../api.h limtorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_lim count_lim.c -lpthread

count_lim_app: count_lim_app.c ../api.h limtorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_lim_app count_lim_app.c -lpthread

count_lim_atomic: count_lim_atomic.c ../api.h limtorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_lim_atomic count_lim_atomic.c -lpthread

count_lim_sig: count_lim_sig.c ../api.h limtorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_lim_sig count_lim_sig.c -lpthread

count_limd: count_limd.c ../api.h limtorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_limd count_limd.c -lpthread

count_nonatomic: count_nonatomic.c ../api.h counttorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_nonatomic count_nonatomic.c -lpthread

count_stack: count_stack.c ../api.h counttorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_stack count_stack.c -lpthread

count_stat: count_stat.c ../api.h counttorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_stat count_stat.c -lpthread

count_stat_atomic: count_stat_atomic.c ../api.h counttorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_stat_atomic count_stat_atomic.c -lpthread

count_stat_eventual: count_stat_eventual.c ../api.h counttorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_stat_eventual count_stat_eventual.c -lpthread

count_tstat: count_tstat.c ../api.h counttorture.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o count_tstat count_tstat.c -lpthread

clean:
	rm -f $(PROGS)
