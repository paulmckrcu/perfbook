#!/bin/bash
#
# Randomly online and offline CPUs.  Requires a recent version of awk
# that supports the systime() function.
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
# Copyright (C) IBM Corporation, 2008
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

while :
do
	cat debug/rcu/rcugp
	{
		cat << '---EOF---'
function onoff { # onoff onlining|offlining 1|0 cpu
	echo $1 $3 `date`
	if echo $2 > /sys/devices/system/cpu/cpu$3/online
	then
		echo done $1 cpu `date`
	else
		sleep 3
		if echo $2 > /sys/devices/system/cpu/cpu$3/online
		then
			echo done $1 $3 `date`
		else
			echo giving up on $1 `date`
		fi
	fi
}
---EOF---
		grep . /dev/null /sys/devices/system/cpu/cpu*/online |
		awk '
			BEGIN {
				srand(systime());
			}

			{
				a[NR] = $0;
			}

			END {
				i = int(rand() * NR) + 1;
				split(a[i], b, ":");
				if (b[2])
					sense = "offlining";
				else
					sense = "onlining";
				cpu = b[1];
				sub("/sys/devices/system/cpu/cpu", "", cpu);
				sub("/online", "", cpu);
				print "onoff", sense, !b[2], cpu
			}'
	} | sh
	cat /sys/devices/system/cpu/cpu*/online | fmt
	cat debug/rcu/rcugp
	sleep 3
done
