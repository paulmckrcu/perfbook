/*
 * Architecture definitions for x86.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; but only under the terms of the variant
 * of GPL covering the Linux kernel (because this contains code extracted
 * from the Linux kernel).
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
 * Copyright (C) IBM Corporation, 2006
 *
 * Authors: Paul E. McKenney <paulmck@us.ibm.com>
 */

/*
 * Memory barriers and atomic instructions.
 */

#define barrier() __asm__ __volatile__ ("" : : : "memory")
#define hwsync() __asm__ __volatile__ ("lock; addl $0,0(%%esp)" : : : "memory")
#define isync() __asm__ __volatile__ ("lock; addl $0,0(%%esp)" : : : "memory")
#define lwsync() __asm__ __volatile__ ("lock; addl $0,0(%%esp)" : : : "memory")
#define eieio() __asm__ __volatile__ ("" : : : "memory")

static inline cisync(long src)
{
	return src;
}

/*
 * Atomic decrement, stolen from Linux kernel.
 */
static __inline__ void atomic_dec(long *v)
{
	__asm__ __volatile__("lock; decl %0" : "+m" (*v));
}

/*
 * Atomic increment, also stolen from Linux kernel.
 */
static __inline__ void atomic_inc(long *v)
{
	__asm__ __volatile__("lock; incl %0" : "+m" (*v));
}

/*
 * Return the lower 32 bits of the time-base register.
 */
static __inline__ long gettb(void)
{
	long t;

	__asm__ __volatile__("rdtsc" : "=a" (t) : : "edx");
	return t;
}
