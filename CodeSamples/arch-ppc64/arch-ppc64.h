/*
 * arch-ppc64.h: Expose PowerPC atomic instructions.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; but version 2 of the License only due
 * to code included from the Linux kernel.
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
#define CONFIG_PPC64

#define CACHE_LINE_SIZE 128
#define ____cacheline_internodealigned_in_smp \
	__attribute__((__aligned__(1 << 7)))

#define smp_lwsync() __asm__ __volatile__(LWSYNC_ON_SMP: : :"memory")

/* Atomic operations are already serializing on x86 */
#define smp_mb__before_atomic_dec()	smp_mb()
#define smp_mb__after_atomic_dec()	smp_mb()
#define smp_mb__before_atomic_inc()	smp_mb()
#define smp_mb__after_atomic_inc()	smp_mb()

#define smp_mb()  __asm__ __volatile__("sync" : : : "memory")


/*
 * Generate 64-bit timestamp.
 */

static __inline__ unsigned long long get_timestamp(void)
{
	unsigned int __a,__d;

	asm volatile("mftbl %0" : "=r" (__a));
	asm volatile("mftbu %0" : "=r" (__d));
	return ((long long)__a) | (((long long)__d)<<32);
}
