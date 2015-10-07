/*
 * Architecture definitions for PPC.
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
#define hwsync() __asm__ __volatile__ ("sync" : : : "memory")
#define isync() __asm__ __volatile__ ("isync" : : : "memory")
#define lwsync() __asm__ __volatile__ ("lwsync" : : : "memory")
#define eieio() __asm__ __volatile__ ("eieio" : : : "memory")

/*
 * Pick up the value pointed to by src, force a branch and isync,
 * then store the value through the pointer dst.
 * @@@ This appears to be broken, both definitions.
 */
#if 0
static inline cisync(long *src, long *dst)
{
	long temp;

	__asm__ __volatile__(
	"lwz	%1,0(%2);"
	"cmpw	0,%1,%1;"
	"bne-	1f;"
"1:	isync;"
	"stw	%1,0(%3);"
	: "=m" (*dst), "=&r" (temp)
	: "r" (src), "r" (dst)
	: "cc");
}
#else
static inline cisync(long src)
{
	__asm__ __volatile__(
	"cmpw	0,%0,%0;"
	"bne-	1f;"
"1:	isync;"
	:
	: "r" (src)
	: "cc");
}
#endif

/*
 * Atomic decrement, stolen from Linux kernel.
 */
static __inline__ void atomic_dec(long *v)
{
	int t;

	__asm__ __volatile__(
"1:	lwarx	%0,0,%2\n\
	subic	%0,%0,1\n\
	stwcx.	%0,0,%2 \n\
	bne-	1b"
	: "=&r" (t), "+m" (*v)
	: "r" (v)
	: "cc");
}

/*
 * Atomic increment, also stolen from Linux kernel.
 */
static __inline__ void atomic_inc(long *v)
{
	int t;

	__asm__ __volatile__(
"1:	lwarx	%0,0,%2\n\
	addic	%0,%0,1\n\
	stwcx.	%0,0,%2 \n\
	bne-	1b"
	: "=&r" (t), "+m" (*v)
	: "r" (v)
	: "cc");
}

/*
 * Return the lower 32 bits of the time-base register.
 */
static __inline__ long gettb(void)
{
	long t;

	__asm__ __volatile__("mftb %0" : "=&r" (t) : : "memory");
	return t;
}
