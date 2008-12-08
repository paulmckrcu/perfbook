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
# Copyright (c) 2008 Paul E. McKenney, IBM Corporation.

GCC_ARGS=-g -O3

# http://www.ibm.com/developerworks/wikis/display/hpccentral/Tuning+options+to+consider+with+gcc#Tuningoptionstoconsiderwithgcc-mcpuandmtune
# GCC_ARGS=-g -O3 -m64 -mcpu=power5 -mtune=power5

all: gettimestamp gettimestampmp rcu rcu64 rcu64_atomicgp rcu_lock rcu_lock_percpu rcu_nest rcu_nest_qs rcu_qs rcu_rcg rcu_rcpg rcu_rcpl rcu_rcpls rcu_ts

gettimestamp: gettimestamp.c ../api.h rcutorture.h
	cc $(GCC_ARGS) -o gettimestamp -DTEST gettimestamp.c -lpthread

gettimestampmp: gettimestampmp.c ../api.h rcutorture.h
	cc $(GCC_ARGS) -o gettimestampmp -DTEST gettimestampmp.c -lpthread

rcu: rcu.c rcu.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu -DTEST rcu.c -lpthread

rcu64: rcu64.c rcu64.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu64 -DTEST rcu64.c -lpthread

rcu64_atomicgp: rcu64_atomicgp.c rcu64_atomicgp.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu64_atomicgp -DTEST rcu64_atomicgp.c -lpthread

rcu_lock: rcu_lock.c rcu_lock.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_lock -DTEST rcu_lock.c -lpthread

rcu_lock_percpu: rcu_lock_percpu.c rcu_lock_percpu.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_lock_percpu -DTEST rcu_lock_percpu.c -lpthread

rcu_nest: rcu_nest.c rcu_nest.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_nest -DTEST rcu_nest.c -lpthread

rcu_nest_qs: rcu_nest_qs.c rcu_nest_qs.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_nest_qs -DTEST rcu_nest_qs.c -lpthread

rcu_qs: rcu_qs.c rcu_qs.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_qs -DTEST rcu_qs.c -lpthread

rcu_rcg: rcu_rcg.c rcu_rcg.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_rcg -DTEST rcu_rcg.c -lpthread

rcu_rcpg: rcu_rcpg.c rcu_rcpg.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_rcpg -DTEST rcu_rcpg.c -lpthread

rcu_rcpl: rcu_rcpl.c rcu_rcpl.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_rcpl -DTEST rcu_rcpl.c -lpthread

rcu_rcpls: rcu_rcpls.c rcu_rcpls.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_rcpls -DTEST rcu_rcpls.c -lpthread

rcu_ts: rcu_ts.c rcu_ts.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_ts -DTEST rcu_ts.c -lpthread
