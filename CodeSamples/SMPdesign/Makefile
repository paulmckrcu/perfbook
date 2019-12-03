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
# Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
# Copyright (c) 2019 Paul E. McKenney, Facebook.

ARCH_INDEPENDENT = smpalloc
ARCH_DEPENDENT = lockdeq lockhdeq locktdeq lockrwdeq matmul matmul_block
PROGS = $(ARCH_DEPENDENT) $(ARCH_INDEPENDENT)

include ../Makefile.arch

top := ..
include $(top)/depends.mk

ifeq ($(strip $(target)),)
all: $(ARCH_INDEPENDENT)
	@echo "### $(ARCH_DEPENDENT) in SMPdesign/ can't be built on arch: '$(arch)'."
else
all: $(PROGS)
endif

include $(top)/recipes.mk

# GCC_ARGS=-g -O3

# http://www.ibm.com/developerworks/wikis/display/hpccentral/Tuning+options+to+consider+with+gcc#Tuningoptionstoconsiderwithgcc-mcpuandmtune
# GCC_ARGS=-g -O3 -m64 -mcpu=power5 -mtune=power5

smpalloc: smpalloc.c ../api.h
	cc $(GCC_ARGS) -g -o smpalloc -DTEST smpalloc.c -lpthread

lockdeq: lockdeq.c deqtorture.h ../api.h
	cc $(GCC_ARGS) -g -o lockdeq -DTEST lockdeq.c -lpthread

lockhdeq: lockhdeq.c deqtorture.h ../api.h
	cc $(GCC_ARGS) -g -o lockhdeq -DTEST lockhdeq.c -lpthread

locktdeq: locktdeq.c deqtorture.h ../api.h
	cc $(GCC_ARGS) -g -o locktdeq -DTEST locktdeq.c -lpthread

lockrwdeq: lockrwdeq.c deqtorture.h ../api.h
	cc $(GCC_ARGS) -g -o lockrwdeq -DTEST lockrwdeq.c -lpthread

matmul: matmul.c ../api.h
	cc $(GCC_ARGS) -g -o matmul -DTEST matmul.c -lpthread

matmul_block: matmul_block.c ../api.h
	cc $(GCC_ARGS) -g -o matmul_block -DTEST matmul_block.c -lpthread

clean:
	rm $(PROGS)
