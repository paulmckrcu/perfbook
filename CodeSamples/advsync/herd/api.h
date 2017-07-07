#ifndef __API_H__
#define __API_H__
#ifndef READ_ONCE
#define READ_ONCE(x) __atomic_load_n(&(x), __ATOMIC_RELAXED)
#define WRITE_ONCE(x, v) __atomic_store_n(&(x), (v), __ATOMIC_RELAXED)
#define smp_mb() __atomic_thread_fence(__ATOMIC_SEQ_CST)
#endif
#endif
