/*
 * api-qnx.h: QNX-specific functions
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.  However, please note that much
 * of the code in this file derives from the Linux kernel, and that such
 * code may not be available except under GPLv2.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2022 Elad Lahav
 */

#include <stdint.h>
#include <sys/neutrino.h>

static inline void run_on(int cpu)
{
	uintptr_t runmask;
	int ret;

	runmask = (1UL << cpu);
	ret = ThreadCtl(_NTO_TCTL_RUNMASK, (void *)runmask);
	if (ret) {
		perror("sched_setaffinity");
		abort();
	}
}
