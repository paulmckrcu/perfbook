/*
 * arch-i386.h: Expose x86 atomic instructions.  80486 and better only.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, but version 2 only due to inclusion
 * of Linux-kernel code.
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
 * Copyright (c) 2006-2019 Paul E. McKenney, IBM.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 *
 * Much code taken from the Linux kernel.  For such code, the option
 * to redistribute under later versions of GPL might not be available.
 */

/*
 * Machine parameters.
 */

#define CONFIG_SMP

#define CACHE_LINE_SIZE 64
#define ____cacheline_internodealigned_in_smp \
	__attribute__((__aligned__(1 << 6)))

#define LOCK_PREFIX "lock ; "

/* These are x86-specific, used by some header files */
#define atomic_clear_mask(mask, addr) \
__asm__ __volatile__(LOCK_PREFIX "andl %0,%1" \
: : "r" (~(mask)),"m" (*addr) : "memory")

#define atomic_set_mask(mask, addr) \
__asm__ __volatile__(LOCK_PREFIX "orl %0,%1" \
: : "r" (mask),"m" (*(addr)) : "memory")

/* Atomic operations are already serializing on x86 */
#define smp_mb__before_atomic_dec()	barrier()
#define smp_mb__after_atomic_dec()	barrier()
#define smp_mb__before_atomic_inc()	barrier()
#define smp_mb__after_atomic_inc()	barrier()

#define smp_mb() \
__asm__ __volatile__("mfence" : : : "memory")
/* __asm__ __volatile__("lock; addl $0,0(%%esp)" : : : "memory") */


/*
 * Generate 64-bit timestamp.
 */

static __inline__ long long get_timestamp(void)
{
	unsigned int __a,__d;

	__asm__ __volatile__("rdtsc" : "=a" (__a), "=d" (__d));
	return ((long long)__a) | (((long long)__d)<<32);
}
