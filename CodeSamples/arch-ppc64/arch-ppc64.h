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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2006 Paul E. McKenney, IBM.
 *
 * Much code taken from the Linux kernel.  For such code, the option
 * to redistribute under later versions of GPL might not be available.
 */

/*
 * Machine parameters.
 */

#define CACHE_LINE_SIZE 128

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

/**
 * atomic_add - add integer to atomic variable
 * @i: integer value to add
 * @v: pointer of type atomic_t
 * 
 * Atomically adds @a to @v.
 */
static __inline__ void atomic_add(int a, atomic_t *v)
{
	int t;

	__asm__ __volatile__(
	"1:	lwarx	%0,0,%3		# atomic_add\n\
		add	%0,%2,%0 \n\
		stwcx.	%0,0,%3 \n\
		bne-	1b"
		: "=&r" (t), "+m" (v->counter)
		: "r" (a), "r" (&v->counter)
		: "cc");
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
	int t;

	__asm__ __volatile__(
	"1:	lwarx	%0,0,%3		# atomic_sub \n\
		subf	%0,%2,%0 \n\
		stwcx.	%0,0,%3 \n\
		bne-	1b"
		: "=&r" (t), "+m" (v->counter)
		: "r" (a), "r" (&v->counter)
		: "cc");
}

static __inline__ atomic_sub_return(int a, atomic_t *v)
{
	int t;

	__asm__ __volatile__(
		"lwsync\n\
	1:	lwarx	%0,0,%2		# atomic_sub_return\n\
		subf	%0,%1,%0\n\
		stwcx.	%0,0,%2 \n\
		bne-	1b \n\
		isync"
		: "=&r" (t)
		: "r" (a), "r" (&v->counter)
		: "cc", "memory");

	return t;
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
	int t;

	__asm__ __volatile__(
		"lwsync \n\
	1:	lwarx	%0,0,%2		 # atomic_add_return \n\
		add	%0,%1,%0 \n\
		stwcx.	%0,0,%2 \n\
		bne-	1b \n\
		isync"
		: "=&r" (t)
		: "r" (a), "r" (&v->counter)
		: "cc", "memory");

	return t;
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

static inline int
cmpxchg(volatile int *ptr, int oldval, int newval)
{
	int retval;

	asm("# atomic_cmpxchg4\n"
	    "lwarx	%0,0,%2\n"
	    "cmpw	cr0,%0,%3\n"
	    "bne-	$+12\n"
	    "stwcx.	%4,0,%2\n"
	    "bne-	$-16\n"
	    "# end atomic_cmpxchg4"
	    : "=&r" (retval), "+m" (*ptr)
	    : "r" (ptr), "r" (oldval), "r" (newval), "m" (*ptr)
	    : "cr0");
	return (retval);
}

#define atomic_cmpxchg(v, old, new) ((int)cmpxchg(&((v)->counter), old, new))
#define atomic_xchg(v, new) (xchg(&((v)->counter), new))

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

	__asm__ __volatile__(
		"lwsync \n\
	1:	lwarx	%0,0,%1		# atomic_add_unless\n\
		cmpd	0,%0,%3 \n\
		beq-	2f \n\
		add	%0,%2,%0 \n\
		stwcx.	%0,0,%1 \n\
		bne-	1b \n\
		isync \n\
		subf	%0,%2,%0 \n\
	2:"
		: "=&r" (t)
		: "r" (&v->counter), "r" (a), "r" (u)
		: "cc", "memory");

	return t != u;
}

#define atomic_inc_not_zero(v) atomic_add_unless((v), 1, 0)

#define atomic_inc_return(v)  (atomic_add_return(1,v))
#define atomic_dec_return(v)  (atomic_sub_return(1,v))

/* Atomic operations are already serializing on x86 */
#define smp_mb__before_atomic_dec()	smp_mb()
#define smp_mb__after_atomic_dec()	smp_mb()
#define smp_mb__before_atomic_inc()	smp_mb()
#define smp_mb__after_atomic_inc()	smp_mb()

#define smp_mb()  __asm__ __volatile__("sync" : : : "memory")


/*
 * Generate 64-bit timestamp.
 */

static unsigned long long get_timestamp(void)
{
	unsigned int __a,__d;

	asm volatile("mftbl %0" : "=r" (__a));
	asm volatile("mftbu %0" : "=r" (__d));
	return ((long long)__a) | (((long long)__d)<<32);
}
