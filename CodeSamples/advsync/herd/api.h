#ifndef __API_H__
#define __API_H__
#ifndef READ_ONCE
#define READ_ONCE(x) __atomic_load_n(&(x), __ATOMIC_RELAXED)
#define WRITE_ONCE(x, v) __atomic_store_n(&(x), (v), __ATOMIC_RELAXED)
#define smp_mb() __atomic_thread_fence(__ATOMIC_SEQ_CST)
#define smp_wmb() __atomic_thread_fence(__ATOMIC_RELEASE) /* outside std. */
#define smp_load_acquire(x) __atomic_load_n(x, __ATOMIC_ACQUIRE)
#define smp_store_release(x, v) __atomic_store_n(x, v, __ATOMIC_RELEASE)
#endif
#endif
