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

PROGS =	bug_rcu_dp \
	gettimestamp \
	gettimestampmp \
	hazptr \
	ptxroute \
	rcu \
	rcu64 \
	rcu64_atomicgp \
	rcu_lock \
	rcu_lock_percpu \
	rcu_nest \
	rcu_nest32 \
	rcu_nest_qs \
	rcu_qs \
	rcu_rcg \
	rcu_rcpg \
	rcu_rcpl \
	rcu_rcpls \
	rcu_sig \
	rcu_ts \
	route_hazptr \
	route_rcu \
	route_seq \
	seqlocktorture \

all: $(PROGS)

# Note that bug_srcu_a is disabled until completed.
bug_srcu_a: bug_srcu_a.c srcu.c ../api.h
	cc $(GCC_ARGS) -o bug_srcu_a -DTEST bug_srcu_a.c -lurcu -lpthread

bug_rcu_dp: bug_rcu_dp.c ../api.h
	cc $(GCC_ARGS) -o bug_rcu_dp -DTEST bug_rcu_dp.c -lurcu -lpthread

gettimestamp: gettimestamp.c ../api.h rcutorture.h
	cc $(GCC_ARGS) -o gettimestamp -DTEST gettimestamp.c -lpthread

gettimestampmp: gettimestampmp.c ../api.h rcutorture.h
	cc $(GCC_ARGS) -o gettimestampmp -DTEST gettimestampmp.c -lpthread

hazptr: hazptr.c hazptr.h ../api.h hazptrtorture.h
	cc $(GCC_ARGS) -o hazptr -DTEST hazptr.c -lpthread

ptxroute: ptxroute.c ../api.h
	cc $(GCC_ARGS) -o ptxroute ptxroute.c -lpthread -lurcu -lurcu-signal

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

rcu_nest32: rcu_nest32.c rcu_nest32.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_nest32 -DTEST rcu_nest32.c -lpthread

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

rcu_sig: rcu_sig.c rcu_sig.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_sig -DTEST rcu_sig.c -lpthread

rcu_ts: rcu_ts.c rcu_ts.h ../api.h rcutorture.h
	cc $(GCC_ARGS) -o rcu_ts -DTEST rcu_ts.c -lpthread

route_hazptr: route_hazptr.c ../api.h routetorture.h
	cc $(GCC_ARGS) -o route_hazptr route_hazptr.c hazptr.c -lpthread

route_rcu: route_rcu.c ../api.h routetorture.h
	cc $(GCC_ARGS) -o route_rcu route_rcu.c -lpthread  -lurcu -lurcu-signal

route_seq: route_seq.c ../api.h routetorture.h
	cc $(GCC_ARGS) -o route_seq route_seq.c -lpthread

seqlocktorture: seqlocktorture.c seqlock.h ../api.h
	cc $(GCC_ARGS) -o seqlocktorture seqlocktorture.c -lpthread

clean:
	rm -f $(PROGS)
