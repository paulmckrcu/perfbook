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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2010 Paul E. McKenney, IBM.
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

/*
 * Atomic data structure, initialization, and access.
 */

typedef struct { volatile int counter; } atomic_t;

#define ATOMIC_INIT(i)  { (i) }

#define atomic_read(v)		((v)->counter)
#define atomic_set(v, i)	(((v)->counter) = (i))

/*
 * Atomic operations.
 */

#define xchg(ptr,x) __sync_lock_test_and_set(ptr, x)
#define xchg_local(ptr,x) xchg(ptr,x)

#define cmpxchg(ptr, o, n) __sync_val_compare_and_swap(ptr, o, n)
#define cmpxchg_local(ptr, o, n) cmpxchg(ptr, o, n)

#define atomic_cmpxchg(v, o, n) (cmpxchg(&((v)->counter), (o), (n)))
#define atomic_xchg(v, new) (xchg(&((v)->counter), new))

/**
 * atomic_add - add integer to atomic variable
 * @i: integer value to add
 * @v: pointer of type atomic_t
 *
 * Atomically adds @a to @v.
 */
static __inline__ void atomic_add(int a, atomic_t *v)
{
	(void)__sync_fetch_and_add(&v->counter, a);
}

/**
 * atomic_sub - subtract the atomic variable
 * @i: integer value to subtract
 * @v: pointer of type atomic_t
 *
 * Atomically subtracts @a from @v.
 */
static __inline__ void atomic_sub(int a, atomic_t *v)
{
	(void)__sync_fetch_and_sub(&v->counter, a);
}

static __inline__ atomic_sub_return(int a, atomic_t *v)
{
	return __sync_sub_and_fetch(&v->counter, a);
}

/**
 * atomic_sub_and_test - subtract value from variable and test result
 * @i: integer value to subtract
 * @v: pointer of type atomic_t
 *
 * Atomically subtracts @i from @v and returns
 * true if the result is zero, or false for all
 * other cases.
 */
static __inline__ int atomic_sub_and_test(int a, atomic_t *v)
{
	return atomic_sub_return(a, v) == 0;
}

/**
 * atomic_inc - increment atomic variable
 * @v: pointer of type atomic_t
 *
 * Atomically increments @v by 1.
 */
static __inline__ void atomic_inc(atomic_t *v)
{
	atomic_add(1, v);
}

/**
 * atomic_dec - decrement atomic variable
 * @v: pointer of type atomic_t
 *
 * Atomically decrements @v by 1.
 */
static __inline__ void atomic_dec(atomic_t *v)
{
	atomic_sub(1, v);
}

/**
 * atomic_dec_and_test - decrement and test
 * @v: pointer of type atomic_t
 *
 * Atomically decrements @v by 1 and
 * returns true if the result is 0, or false for all other
 * cases.
 */
static __inline__ int atomic_dec_and_test(atomic_t *v)
{
	return atomic_sub_and_test(1, v);
}

/**
 * atomic_inc_and_test - increment and test
 * @v: pointer of type atomic_t
 *
 * Atomically increments @v by 1
 * and returns true if the result is zero, or false for all
 * other cases.
 */
static __inline__ int atomic_inc_and_test(atomic_t *v)
{
	return atomic_inc_return(v);
}

/**
 * atomic_add_return - add and return
 * @v: pointer of type atomic_t
 * @i: integer value to add
 *
 * Atomically adds @i to @v and returns @i + @v
 */
static __inline__ int atomic_add_return(int a, atomic_t *v)
{
	return __sync_add_and_fetch(&v->counter, a);
}

/**
 * atomic_add_negative - add and test if negative
 * @v: pointer of type atomic_t
 * @i: integer value to add
 *
 * Atomically adds @i to @v and returns true
 * if the result is negative, or false when
 * result is greater than or equal to zero.
 */
static __inline__ int atomic_add_negative(int a, atomic_t *v)
{
	return atomic_add_return(a, v) < 0;
}

/**
 * atomic_add_unless - add unless the number is a given value
 * @v: pointer of type atomic_t
 * @a: the amount to add to v...
 * @u: ...unless v is equal to u.
 *
 * Atomically adds @a to @v, so long as it was not @u.
 * Returns non-zero if @v was not @u, and zero otherwise.
 */
static __inline__ int atomic_add_unless(atomic_t *v, int a, int u)
{
	int t;

	do {
		t = v->counter;
		if (t == u)
			return 0;
	} while (__sync_val_compare_and_swap(&v->counter, t, t + a));
	return 1;
}

#define atomic_inc_not_zero(v) atomic_add_unless((v), 1, 0)

#define atomic_inc_return(v)  (atomic_add_return(1,v))
#define atomic_dec_return(v)  (atomic_sub_return(1,v))

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
