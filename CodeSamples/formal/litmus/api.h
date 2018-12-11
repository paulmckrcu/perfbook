#ifndef __API_H__
#define __API_H__
#ifndef READ_ONCE
#define __READ_ONCE(x) __atomic_load_n((typeof(x) *)&(x), __ATOMIC_RELAXED)
#ifdef __alpha__
#define READ_ONCE(x) ({ typeof(x) ___x = __READ_ONCE(x); smp_mb(); ___x; })
#else
#define READ_ONCE(x) __READ_ONCE(x)
#endif
#define WRITE_ONCE(x, v) __atomic_store_n((typeof(x) *)&(x), (v), __ATOMIC_RELAXED)
#define smp_mb() __atomic_thread_fence(__ATOMIC_SEQ_CST)
#define smp_rmb() __atomic_thread_fence(__ATOMIC_ACQUIRE) /* outside std. */
#define smp_wmb() __atomic_thread_fence(__ATOMIC_RELEASE) /* outside std. */
#define smp_load_acquire(x) __atomic_load_n(x, __ATOMIC_ACQUIRE)
#define smp_store_release(x, v) __atomic_store_n(x, v, __ATOMIC_RELEASE)
#define smp_load_acquire(x) __atomic_load_n(x, __ATOMIC_ACQUIRE)
#define cmpxchg(x, o, n) ({ \
	typeof(o) __old = (o); \
	__atomic_compare_exchange_n((x), &__old, (n), 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED); \
	__old; \
})
#endif
#endif
