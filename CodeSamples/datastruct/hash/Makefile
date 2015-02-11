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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
#
# Copyright (c) 2013 Paul E. McKenney, IBM Corporation.

include ../../Makefile.arch

PROGS =	hash_bkt hash_bkt_hazptr hash_bkt_rcu hash_global hash_resize

all: $(PROGS)

hash_bkt: hash_bkt.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -o hash_bkt hash_bkt.c -lpthread

hash_bkt_rcu: hash_bkt_rcu.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -o hash_bkt_rcu hash_bkt_rcu.c -lpthread -lurcu -lurcu-signal
	# cc $(GCC_ARGS) -o hash_bkt_rcu hash_bkt_rcu.c -lpthread -lurcu -lurcu-qsbr

hash_bkt_hazptr: hash_bkt_hazptr.c ../../defer/hazptr.c ../../defer/hazptr.h ../../api.h hashtorture.h
	cc $(GCC_ARGS) -o hash_bkt_hazptr hash_bkt_hazptr.c ../../defer/hazptr.c -lpthread

hash_global: hash_global.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -o hash_global hash_global.c -lpthread

hash_resize: hash_resize.c ../../api.h hashtorture.h
	cc $(GCC_ARGS) -o hash_resize hash_resize.c -lpthread -lurcu -lurcu-signal

clean:
	rm -f $(PROGS)
