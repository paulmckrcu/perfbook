/*
 * Architecture definitions for IA64.
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
#define hwsync() __asm__ __volatile__ ("mf" : : : "memory")
#define isync() __asm__ __volatile__ ("srlz.d" : : : "memory")
#define lwsync() __asm__ __volatile__ ("mf" : : : "memory")
#define eieio() __asm__ __volatile__ ("mf" : : : "memory")

/*
 * Atomic decrement.
 */
static __inline__ void atomic_dec(long *v)
{
        long ia64_intri_res;
        asm volatile ("fetchadd4.rel %0=[%1],-1"
                                : "=r"(ia64_intri_res) : "r"(v)
                                : "memory");
}

/*
 * Atomic increment -- not used, so skip for now.
 */
static __inline__ void atomic_inc(long *v)
{
        long ia64_intri_res;
        asm volatile ("fetchadd4.rel %0=[%1],1"
                                : "=r"(ia64_intri_res) : "r"(v)
                                : "memory");
}

/*
 * Return the lower 32 bits of the time-base register.
 */
static __inline__ long gettb(void)
{
	long t;

	__asm__ __volatile__("mov %0=ar44" : "=&r" (t) : : "memory");
	return t;
}
