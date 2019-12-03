/*
 * arch-arm.h: Expose ARM atomic instructions.
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
 * Copyright (c) 2010-2019 Paul E. McKenney, IBM.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 *
 * Much code taken from the Linux kernel.  For such code, the option
 * to redistribute under later versions of GPL might not be available.
 */

/*
 * Machine parameters.
 */

#define CONFIG_SMP
#define CONFIG_ARM

#define CACHE_LINE_SIZE 128
#define ____cacheline_internodealigned_in_smp \
	__attribute__((__aligned__(1 << 7)))

/* The gcc primitives imply full memory barriers. */
#define smp_mb__before_atomic_dec()	do { } while (0)
#define smp_mb__after_atomic_dec()	do { } while (0)
#define smp_mb__before_atomic_inc()	do { } while (0)
#define smp_mb__after_atomic_inc()	do { } while (0)

/* __sync_synchronize() is broken before gcc 4.4.1 on many ARM systems. */
#define smp_mb()  __asm__ __volatile__("dmb" : : : "memory")


#include <stdlib.h>
#include <sys/time.h>

/*
 * Generate 64-bit timestamp.
 */
static __inline__ unsigned long long get_timestamp(void)
{
	unsigned long long thetime;
	struct timeval tv;

	if (gettimeofday(&tv, NULL) != 0)
		return 0;
	thetime = ((unsigned long long)tv.tv_sec) * 1000000ULL +
		  ((unsigned long long)tv.tv_usec);
	return thetime;
}
