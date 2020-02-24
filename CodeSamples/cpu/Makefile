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

PROGS =	cachetorture

top := ..
include $(top)/depends.mk

ifeq ($(strip $(target)),)
all:
	@echo "### None in cpu/ can be built on arch: '$(arch)'."
else
all: $(PROGS)
endif

CC?=cc

include $(top)/recipes.mk

cachetorture: cachetorture.c ../api.h
	$(CC) $(GCC_ARGS) $(CFLAGS) -o cachetorture cachetorture.c -lpthread

clean:
	rm -f $(PROGS)
