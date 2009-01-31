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

#define CONFIG_SMP
#define CONFIG_PPC64

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

#define LWSYNC lwsync
#define PPC405_ERR77(ra,rb)
#ifdef CONFIG_SMP
#  define LWSYNC_ON_SMP stringify_in_c(LWSYNC) "\n"
#  define ISYNC_ON_SMP "\n\tisync\n"
#else
#  define LWSYNC_ON_SMP
#  define ISYNC_ON_SMP
#endif


/*
 * Atomic exchange
 *
 * Changes the memory location '*ptr' to be val and returns
 * the previous value stored there.
 */
static __always_inline unsigned long
__xchg_u32(volatile void *p, unsigned long val)
{
	unsigned long prev;

	__asm__ __volatile__(
	LWSYNC_ON_SMP
"1:	lwarx	%0,0,%2 \n"
	PPC405_ERR77(0,%2)
"	stwcx.	%3,0,%2 \n\
	bne-	1b"
	ISYNC_ON_SMP
	: "=&r" (prev), "+m" (*(volatile unsigned int *)p)
	: "r" (p), "r" (val)
	: "cc", "memory");

	return prev;
}

/*
 * Atomic exchange
 *
 * Changes the memory location '*ptr' to be val and returns
 * the previous value stored there.
 */
static __always_inline unsigned long
__xchg_u32_local(volatile void *p, unsigned long val)
{
	unsigned long prev;

	__asm__ __volatile__(
"1:	lwarx	%0,0,%2 \n"
	PPC405_ERR77(0,%2)
"	stwcx.	%3,0,%2 \n\
	bne-	1b"
	: "=&r" (prev), "+m" (*(volatile unsigned int *)p)
	: "r" (p), "r" (val)
	: "cc", "memory");

	return prev;
}

#ifdef CONFIG_PPC64
static __always_inline unsigned long
__xchg_u64(volatile void *p, unsigned long val)
{
	unsigned long prev;

	__asm__ __volatile__(
	LWSYNC_ON_SMP
"1:	ldarx	%0,0,%2 \n"
	PPC405_ERR77(0,%2)
"	stdcx.	%3,0,%2 \n\
	bne-	1b"
	ISYNC_ON_SMP
	: "=&r" (prev), "+m" (*(volatile unsigned long *)p)
	: "r" (p), "r" (val)
	: "cc", "memory");

	return prev;
}

static __always_inline unsigned long
__xchg_u64_local(volatile void *p, unsigned long val)
{
	unsigned long prev;

	__asm__ __volatile__(
"1:	ldarx	%0,0,%2 \n"
	PPC405_ERR77(0,%2)
"	stdcx.	%3,0,%2 \n\
	bne-	1b"
	: "=&r" (prev), "+m" (*(volatile unsigned long *)p)
	: "r" (p), "r" (val)
	: "cc", "memory");

	return prev;
}
#endif

/*
 * This function doesn't exist, so you'll get a linker error
 * if something tries to do an invalid xchg().
 */
extern void __xchg_called_with_bad_pointer(void);

static __always_inline unsigned long
__xchg(volatile void *ptr, unsigned long x, unsigned int size)
{
	switch (size) {
	case 4:
		return __xchg_u32(ptr, x);
#ifdef CONFIG_PPC64
	case 8:
		return __xchg_u64(ptr, x);
#endif
	}
	__xchg_called_with_bad_pointer();
	return x;
}

static __always_inline unsigned long
__xchg_local(volatile void *ptr, unsigned long x, unsigned int size)
{
	switch (size) {
	case 4:
		return __xchg_u32_local(ptr, x);
#ifdef CONFIG_PPC64
	case 8:
		return __xchg_u64_local(ptr, x);
#endif
	}
	__xchg_called_with_bad_pointer();
	return x;
}
#define xchg(ptr,x)							     \
  ({									     \
     __typeof__(*(ptr)) _x_ = (x);					     \
     (__typeof__(*(ptr))) __xchg((ptr), (unsigned long)_x_, sizeof(*(ptr))); \
  })

#define xchg_local(ptr,x)						     \
  ({									     \
     __typeof__(*(ptr)) _x_ = (x);					     \
     (__typeof__(*(ptr))) __xchg_local((ptr),				     \
     		(unsigned long)_x_, sizeof(*(ptr))); 			     \
  })

/*
 * Compare and exchange - if *p == old, set it to new,
 * and return the old value of *p.
 */
#define __HAVE_ARCH_CMPXCHG	1

static __always_inline unsigned long
__cmpxchg_u32(volatile unsigned int *p, unsigned long old, unsigned long new)
{
	unsigned int prev;

	__asm__ __volatile__ (
	LWSYNC_ON_SMP
"1:	lwarx	%0,0,%2		# __cmpxchg_u32\n\
	cmpw	0,%0,%3\n\
	bne-	2f\n"
	PPC405_ERR77(0,%2)
"	stwcx.	%4,0,%2\n\
	bne-	1b"
	ISYNC_ON_SMP
	"\n\
2:"
	: "=&r" (prev), "+m" (*p)
	: "r" (p), "r" (old), "r" (new)
	: "cc", "memory");

	return prev;
}

static __always_inline unsigned long
__cmpxchg_u32_local(volatile unsigned int *p, unsigned long old,
			unsigned long new)
{
	unsigned int prev;

	__asm__ __volatile__ (
"1:	lwarx	%0,0,%2		# __cmpxchg_u32\n\
	cmpw	0,%0,%3\n\
	bne-	2f\n"
	PPC405_ERR77(0,%2)
"	stwcx.	%4,0,%2\n\
	bne-	1b"
	"\n\
2:"
	: "=&r" (prev), "+m" (*p)
	: "r" (p), "r" (old), "r" (new)
	: "cc", "memory");

	return prev;
}

#ifdef CONFIG_PPC64
static __always_inline unsigned long
__cmpxchg_u64(volatile unsigned long *p, unsigned long old, unsigned long new)
{
	unsigned long prev;

	__asm__ __volatile__ (
	LWSYNC_ON_SMP
"1:	ldarx	%0,0,%2		# __cmpxchg_u64\n\
	cmpd	0,%0,%3\n\
	bne-	2f\n\
	stdcx.	%4,0,%2\n\
	bne-	1b"
	ISYNC_ON_SMP
	"\n\
2:"
	: "=&r" (prev), "+m" (*p)
	: "r" (p), "r" (old), "r" (new)
	: "cc", "memory");

	return prev;
}

static __always_inline unsigned long
__cmpxchg_u64_local(volatile unsigned long *p, unsigned long old,
			unsigned long new)
{
	unsigned long prev;

	__asm__ __volatile__ (
"1:	ldarx	%0,0,%2		# __cmpxchg_u64\n\
	cmpd	0,%0,%3\n\
	bne-	2f\n\
	stdcx.	%4,0,%2\n\
	bne-	1b"
	"\n\
2:"
	: "=&r" (prev), "+m" (*p)
	: "r" (p), "r" (old), "r" (new)
	: "cc", "memory");

	return prev;
}
#endif

/* This function doesn't exist, so you'll get a linker error
   if something tries to do an invalid cmpxchg().  */
extern void __cmpxchg_called_with_bad_pointer(void);

static __always_inline unsigned long
__cmpxchg(volatile void *ptr, unsigned long old, unsigned long new,
	  unsigned int size)
{
	switch (size) {
	case 4:
		return __cmpxchg_u32(ptr, old, new);
#ifdef CONFIG_PPC64
	case 8:
		return __cmpxchg_u64(ptr, old, new);
#endif
	}
	__cmpxchg_called_with_bad_pointer();
	return old;
}

static __always_inline unsigned long
__cmpxchg_local(volatile void *ptr, unsigned long old, unsigned long new,
	  unsigned int size)
{
	switch (size) {
	case 4:
		return __cmpxchg_u32_local(ptr, old, new);
#ifdef CONFIG_PPC64
	case 8:
		return __cmpxchg_u64_local(ptr, old, new);
#endif
	}
	__cmpxchg_called_with_bad_pointer();
	return old;
}

#define cmpxchg(ptr, o, n)						 \
  ({									 \
     __typeof__(*(ptr)) _o_ = (o);					 \
     __typeof__(*(ptr)) _n_ = (n);					 \
     (__typeof__(*(ptr))) __cmpxchg((ptr), (unsigned long)_o_,		 \
				    (unsigned long)_n_, sizeof(*(ptr))); \
  })


#define cmpxchg_local(ptr, o, n)					 \
  ({									 \
     __typeof__(*(ptr)) _o_ = (o);					 \
     __typeof__(*(ptr)) _n_ = (n);					 \
     (__typeof__(*(ptr))) __cmpxchg_local((ptr), (unsigned long)_o_,	 \
				    (unsigned long)_n_, sizeof(*(ptr))); \
  })

#ifdef CONFIG_PPC64
/*
 * We handle most unaligned accesses in hardware. On the other hand 
 * unaligned DMA can be very expensive on some ppc64 IO chips (it does
 * powers of 2 writes until it reaches sufficient alignment).
 *
 * Based on this we disable the IP header alignment in network drivers.
 * We also modify NET_SKB_PAD to be a cacheline in size, thus maintaining
 * cacheline alignment of buffers.
 */
#define NET_IP_ALIGN	0
#define NET_SKB_PAD	L1_CACHE_BYTES

#define cmpxchg64(ptr, o, n)						\
  ({									\
	BUILD_BUG_ON(sizeof(*(ptr)) != 8);				\
	cmpxchg((ptr), (o), (n));					\
  })
#define cmpxchg64_local(ptr, o, n)					\
  ({									\
	BUILD_BUG_ON(sizeof(*(ptr)) != 8);				\
	cmpxchg_local((ptr), (o), (n));					\
  })
#endif

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
