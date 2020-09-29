/*
 * api-gcc.h: API mapping to pthreads gcc environment.
 *	Uses C11-like gcc intrinsics.
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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

/*
 * Atomic data structure, initialization, and access.
 */

typedef struct { volatile int counter; } atomic_t;

#define ATOMIC_INIT(i)  { (i) }

#define atomic_read(v) \
	__atomic_load_n(&(v)->counter, __ATOMIC_RELAXED)
#define atomic_set(v, i) \
	__atomic_store_n(&(v)->counter, (i), __ATOMIC_RELAXED)
#define smp_load_acquire(p) \
	__atomic_load_n(p, __ATOMIC_ACQUIRE)
#define smp_store_release(p, i) \
	__atomic_store_n(p, (i), __ATOMIC_RELEASE)

/*
 * Atomic operations.
 */

/**
 * atomic_add - add integer to atomic variable
 * @i: integer value to add
 * @v: pointer of type atomic_t
 *
 * Atomically adds @i to @v.
 */
static __inline__ void atomic_add(int i, atomic_t *v)
{
	__atomic_add_fetch(&v->counter, i, __ATOMIC_RELAXED);
}

/**
 * atomic_sub - subtract the atomic variable
 * @i: integer value to subtract
 * @v: pointer of type atomic_t
 *
 * Atomically subtracts @i from @v.
 */
static __inline__ void atomic_sub(int i, atomic_t *v)
{
	__atomic_sub_fetch(&v->counter, i, __ATOMIC_RELAXED);
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
static __inline__ int atomic_sub_and_test(int i, atomic_t *v)
{
	return __atomic_sub_fetch(&v->counter, i, __ATOMIC_SEQ_CST) == 0;
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
	return __atomic_add_fetch(&v->counter, 1, __ATOMIC_SEQ_CST) == 0;
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
static __inline__ int atomic_add_negative(int i, atomic_t *v)
{
	return __atomic_add_fetch(&v->counter, i, __ATOMIC_SEQ_CST) < 0;
}

/**
 * atomic_add_return - add and return
 * @v: pointer of type atomic_t
 * @i: integer value to add
 *
 * Atomically adds @i to @v and returns @i + @v
 */
static __inline__ int atomic_add_return(int i, atomic_t *v)
{
	return __atomic_add_fetch(&v->counter, i, __ATOMIC_SEQ_CST);
}

static __inline__ int atomic_sub_return(int i, atomic_t *v)
{
	return atomic_add_return(-i, v);
}

struct __xchg_dummy {
	unsigned long a[100];
};
#define __xg(x) ((struct __xchg_dummy *)(x))

#define cmpxchg(ptr, o, n) \
({ \
	typeof(*ptr) _____actual = (o); \
	\
	__atomic_compare_exchange_n((ptr), (void *)&_____actual, (n), 0, \
			__ATOMIC_SEQ_CST, __ATOMIC_RELAXED); \
	_____actual; \
})

static __inline__ int atomic_cmpxchg(atomic_t *v, int old, int new)
{
	return cmpxchg(&v->counter, old, new);
}

#define xchg(ptr, v) __atomic_exchange_n((ptr), (v), __ATOMIC_SEQ_CST)
#define atomic_xchg(ptr, v) \
	__atomic_exchange_n(&(ptr)->counter, (v), __ATOMIC_SEQ_CST)

/**
 * atomic_add_unless - add unless the number is a given value
 * @v: pointer of type atomic_t
 * @a: the amount to add to v...
 * @u: ...unless v is equal to u.
 *
 * Atomically adds @a to @v, so long as it was not @u.
 * Returns non-zero if @v was not @u, and zero otherwise.
 */
#define atomic_add_unless(v, a, u)				\
({								\
	int c, old;						\
	c = atomic_read(v);					\
	for (;;) {						\
		if (unlikely(c == (u)))				\
			break;					\
		old = atomic_cmpxchg((v), c, c + (a));		\
		if (likely(old == c))				\
			break;					\
		c = old;					\
	}							\
	c != (u);						\
})
#define atomic_inc_not_zero(v) atomic_add_unless((v), 1, 0)

#define atomic_inc_return(v)  (atomic_add_return(1,v))
#define atomic_dec_return(v)  (atomic_sub_return(1,v))
