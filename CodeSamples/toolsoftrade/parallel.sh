#!/bin/sh
#
# Example parallel and pipelined shell script.
#
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
# Copyright (C) IBM Corporation, 2009-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

# We cheat and substitute a 5-second sleep for useful computation.
function compute_it {
	echo computing $1
	sleep 5
}

# \begin{snippet}[labelbase=ln:toolsoftrade:parallel:compute_it,commandchars=\\\{\},style=N]
echo Computing in parallel starting at `date`	#\fcvexclude
compute_it 1 > compute_it.1.out &		#\lnlbl{comp1}
compute_it 2 > compute_it.2.out &		#\lnlbl{comp2}
wait						#\lnlbl{wait}
echo Computing in parallel finished at `date`	#\fcvexclude
echo Computation \"output\":			#\fcvexclude
cat compute_it.1.out				#\lnlbl{cat1}
cat compute_it.2.out				#\lnlbl{cat2}
rm compute_it.1.out compute_it.2.out		#\fcvexclude
# \end{snippet}

echo
echo Computing sequentially starting at `date`
compute_it 1 > compute_it.1.out
compute_it 2 > compute_it.2.out
echo Computing sequentially finished at `date`
echo Computation \"output\":
cat compute_it.1.out
cat compute_it.2.out
rm compute_it.1.out compute_it.2.out

echo
echo Computing in pipeline starting at `date`
compute_it 1 | compute_it 2 > compute_it.out
echo Computing in pipeline finished at `date`
echo Computation \"output\":
cat compute_it.out
rm compute_it.out
