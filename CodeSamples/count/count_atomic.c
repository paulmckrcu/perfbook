/*
 * count_atomic.c: simple atomic counter.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
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
 * Copyright (c) 2009-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include "../api.h"

//\begin{snippet}[labelbase=ln:count:count_atomic:inc-read,commandchars=\\\[\]]
atomic_t counter = ATOMIC_INIT(0);		//\lnlbl{counter}

static __inline__ void inc_count(void)
{
	atomic_inc(&counter);			//\lnlbl{inc}
}

static __inline__ long read_count(void)
{
	return atomic_read(&counter);		//\lnlbl{read}
}
//\end{snippet}

static __inline__ void count_init(void)
{
}

static __inline__ void count_cleanup(void)
{
}

#include "counttorture.h"
