/*
 * api_pthreads.h: API mapping to pthreads environment.
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
 * Copyright (c) 2006-2019 Paul E. McKenney, IBM.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <errno.h>
#include <limits.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include <string.h>
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif /* #ifndef _GNU_SOURCE */
#ifndef __USE_GNU
#define __USE_GNU
#endif /* #ifndef __USE_GNU */
#include <pthread.h>
#include <sched.h>
#include <sys/param.h>
/* #include "atomic.h" */

/*
 * Compiler magic.
 */
#ifndef offsetof
#define offsetof(TYPE, MEMBER) ((size_t) &((TYPE *)0)->MEMBER)
#endif /* #ifndef offsetof */
#ifndef container_of
#define container_of(ptr, type, member) ({			\
	const typeof( ((type *)0)->member ) *__mptr = (ptr);	\
	(type *)( (char *)__mptr - offsetof(type,member) );})
#endif /* #ifndef offsetof */

/*
 * Default machine parameters.
 */

#ifndef CACHE_LINE_SIZE
#define CACHE_LINE_SIZE 128
#endif /* #ifndef CACHE_LINE_SIZE */

/*
 * Exclusive locking primitives.
 */

typedef pthread_mutex_t spinlock_t;

#define DEFINE_SPINLOCK(lock) spinlock_t lock = PTHREAD_MUTEX_INITIALIZER;
#define __SPIN_LOCK_UNLOCKED(lockp) PTHREAD_MUTEX_INITIALIZER

static __inline__ void spin_lock_init(spinlock_t *sp)
{
	int ret;

retry:
	ret = pthread_mutex_init(sp, NULL);
	if (ret) {
		if (ret == EINTR)
			goto retry;
		fprintf(stderr, "spin_lock_init:pthread_mutex_init %d\n", ret);
		abort();
	}
}

static __inline__ void spin_lock(spinlock_t *sp)
{
	int en;

	en = pthread_mutex_lock(sp);
	if (en != 0) {
		fprintf(stderr, "pthread_mutex_lock: %s\n", strerror(en));
		perror("spin_lock:pthread_mutex_lock");
		abort();
	}
}

static __inline__ int spin_trylock(spinlock_t *sp)
{
	int retval;

	if ((retval = pthread_mutex_trylock(sp)) == 0)
		return 1;
	if (retval == EBUSY)
		return 0;
	fprintf(stderr, "pthread_mutex_trylock: %s\n", strerror(retval));
	abort();
}

static __inline__ void spin_unlock(spinlock_t *sp)
{
	int en;

	en = pthread_mutex_unlock(sp);
	if (en != 0) {
		fprintf(stderr, "pthread_mutex_unlock: %s\n", strerror(en));
		abort();
	}
}

static __inline__ int spin_is_locked(spinlock_t *sp)
{
	if (spin_trylock(sp)) {
		spin_unlock(sp);
		return 0;
	}
	return 1;
}

#define spin_lock_irqsave(l, f) do { f = 1; spin_lock(l); } while (0)
#define spin_unlock_irqrestore(l, f) do { f = 0; spin_unlock(l); } while (0)

//\begin{snippet}[labelbase=ln:api-pthreads:api-pthreads:compiler_barrier,commandchars=\@\[\],numbers=none,xleftmargin=0pt]
#define ACCESS_ONCE(x) (*(volatile typeof(x) *)&(x))
#define READ_ONCE(x) \
                ({ typeof(x) ___x = ACCESS_ONCE(x); ___x; })
#define WRITE_ONCE(x, val) \
                do { ACCESS_ONCE(x) = (val); } while (0)
#define barrier() __asm__ __volatile__("": : :"memory")
//\end{snippet}
#ifndef unlikely
#define unlikely(x) x
#endif /* #ifndef unlikely */
#ifndef likely
#define likely(x) x
#endif /* #ifndef likely */
#define prefetch(x) x

/*
 * Thread creation/destruction primitives.
 */

typedef pthread_t thread_id_t;

#define NR_THREADS 512

#define __THREAD_ID_MAP_EMPTY 0
#define __THREAD_ID_MAP_WAITING 1
thread_id_t __thread_id_map[NR_THREADS];
spinlock_t __thread_id_map_mutex;

#define for_each_thread(t) \
	for (t = 0; t < NR_THREADS; t++)

#define for_each_running_thread(t) \
	for (t = 0; t < NR_THREADS; t++) \
		if ((__thread_id_map[t] != __THREAD_ID_MAP_EMPTY) && \
		    (__thread_id_map[t] != __THREAD_ID_MAP_WAITING))

#define for_each_tid(t, tid) \
	for (t = 0; t < NR_THREADS; t++) \
		if ((((tid) = __thread_id_map[t]) != __THREAD_ID_MAP_EMPTY) && \
		    ((tid) != __THREAD_ID_MAP_WAITING))

pthread_key_t thread_id_key;

static __inline__ int num_online_threads(void)
{
	int t;
	int nonline = 0;

	for_each_running_thread(t)
		nonline++;
	return nonline;
}

static __inline__ int __smp_thread_id(void)
{
	int i;
	thread_id_t tid = pthread_self();

	for (i = 0; i < NR_THREADS; i++) {
		if (__thread_id_map[i] == tid) {
			long v = i + 1;  /* must be non-NULL. */

			if (pthread_setspecific(thread_id_key, (void *)v) != 0) {
				perror("pthread_setspecific");
				exit(EXIT_FAILURE);
			}
			return i;
		}
	}
	spin_lock(&__thread_id_map_mutex);
	for (i = 0; i < NR_THREADS; i++) {
		if (__thread_id_map[i] == tid) {
			spin_unlock(&__thread_id_map_mutex);
			return i;
		}
	}
	spin_unlock(&__thread_id_map_mutex);
	fprintf(stderr, "smp_thread_id: Rogue thread, id: %d(%#x)\n",
		(int)tid, (int)tid);
	exit(EXIT_FAILURE);
}

static __inline__ int smp_thread_id(void)
{
	void *id;

	id = pthread_getspecific(thread_id_key);
	if (id == NULL)
		return __smp_thread_id();
	return (long)(id - 1);
}

static __inline__ thread_id_t create_thread(void *(*func)(void *), void *arg)
{
	thread_id_t tid;
	int i;

	spin_lock(&__thread_id_map_mutex);
	for (i = 0; i < NR_THREADS; i++) {
		if (__thread_id_map[i] == __THREAD_ID_MAP_EMPTY)
			break;
	}
	if (i >= NR_THREADS) {
		spin_unlock(&__thread_id_map_mutex);
		fprintf(stderr, "Thread limit of %d exceeded!\n", NR_THREADS);
		exit(EXIT_FAILURE);
	}
	__thread_id_map[i] = __THREAD_ID_MAP_WAITING;
	if (pthread_create(&tid, NULL, func, arg) != 0) {
		perror("create_thread:pthread_create");
		exit(EXIT_FAILURE);
	}
	__thread_id_map[i] = tid;
	spin_unlock(&__thread_id_map_mutex);
	return tid;
}

static __inline__ void *wait_thread(thread_id_t tid)
{
	int i;
	void *vp;

	for (i = 0; i < NR_THREADS; i++) {
		if (__thread_id_map[i] == tid)
			break;
	}
	if (i >= NR_THREADS){
		fprintf(stderr, "wait_thread: bad tid = %d(%#x)\n",
			(int)tid, (int)tid);
		exit(EXIT_FAILURE);
	}
	if (pthread_join(tid, &vp) != 0) {
		perror("wait_thread:pthread_join");
		exit(EXIT_FAILURE);
	}
	__thread_id_map[i] = __THREAD_ID_MAP_EMPTY;
	return vp;
}

static __inline__ void wait_all_threads(void)
{
	int i;
	thread_id_t tid;

	for (i = 1; i < NR_THREADS; i++) {
		tid = __thread_id_map[i];
		if (tid != __THREAD_ID_MAP_EMPTY &&
		    tid != __THREAD_ID_MAP_WAITING)
			(void)wait_thread(tid);
	}
}

/*
 * Wait on all child processes.
 */
// \begin{snippet}[labelbase=ln:api-pthreads:api-pthreads:waitall,commandchars=\%\[\]]
static __inline__ void waitall(void)
{
	int pid;
	int status;

	for (;;) {				//\lnlbl{loopa}
		pid = wait(&status);		//\lnlbl{wait}
		if (pid == -1) {
			if (errno == ECHILD)	//\lnlbl{ECHILD}
				break;		//\lnlbl{break}
			perror("wait");		//\lnlbl{perror}
			exit(EXIT_FAILURE);	//\lnlbl{exit}
		}
		poll(NULL, 0, 1);		//\fcvexclude
	}					//\lnlbl{loopb}
}
// \end{snippet}

static __inline__ void run_on(int cpu)
{
	cpu_set_t mask;
	int ret;

	CPU_ZERO(&mask);
	CPU_SET(cpu, &mask);
	ret = sched_setaffinity(0, sizeof(mask), &mask);
	if (ret) {
		perror("sched_setaffinity");
		abort();
	}
}

/*
 * Timekeeping, using monotonic globally coherent clock.
 */

static __inline__ long long get_microseconds(void)
{
	struct timespec ts;

	if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0)
		abort();
	return ((long long)ts.tv_sec) * 1000000LL +
	       (long long)ts.tv_nsec / 1000LL;
}

/*
 * Per-thread variables.
 */

#define DEFINE_PER_THREAD(type, name) \
	struct { \
		__typeof__(type) v \
			__attribute__((__aligned__(CACHE_LINE_SIZE))); \
	} __per_thread_##name[NR_THREADS];
#define DECLARE_PER_THREAD(type, name) extern DEFINE_PER_THREAD(type, name)

#define per_thread(name, thread) __per_thread_##name[thread].v
#define __get_thread_var(name) per_thread(name, smp_thread_id())

#define init_per_thread(name, v) \
	do { \
		int __i_p_t_i; \
		for (__i_p_t_i = 0; __i_p_t_i < NR_THREADS; __i_p_t_i++) \
			per_thread(name, __i_p_t_i) = v; \
	} while (0)

/*
 * CPU traversal primitives.
 */

#ifndef NR_CPUS
#define NR_CPUS 16
#endif /* #ifndef NR_CPUS */

#define for_each_possible_cpu(cpu) \
	for (cpu = 0; cpu < NR_CPUS; cpu++)
#define for_each_online_cpu(cpu) \
	for (cpu = 0; cpu < NR_CPUS; cpu++)

/*
 * Per-CPU variables.
 */

#define DEFINE_PER_CPU(type, name) \
	struct { \
		__typeof__(type) v \
			__attribute__((__aligned__(CACHE_LINE_SIZE))); \
	} __per_cpu_##name[NR_CPUS]
#define DECLARE_PER_CPU(type, name) extern DEFINE_PER_CPU(type, name)

DEFINE_PER_THREAD(int, smp_processor_id);

static __inline__ int smp_processor_id(void)
{
	return __get_thread_var(smp_processor_id);
}

static __inline__ void set_smp_processor_id(int cpu)
{
	__get_thread_var(smp_processor_id) = cpu;
}

#define per_cpu(name, thread) __per_cpu_##name[thread].v
#define __get_cpu_var(name) per_cpu(name, smp_processor_id())

#define init_per_cpu(name, v) \
	do { \
		int __i_p_c_i; \
		for (__i_p_c_i = 0; __i_p_c_i < NR_CPUS; __i_p_c_i++) \
			per_cpu(name, __i_p_c_i) = v; \
	} while (0)

/*
 * CPU state checking (crowbarred).
 */

#define idle_cpu(cpu) 0
#define in_softirq() 1
#define hardirq_count() 0
#define PREEMPT_SHIFT   0
#define SOFTIRQ_SHIFT   (PREEMPT_SHIFT + PREEMPT_BITS)
#define HARDIRQ_SHIFT   (SOFTIRQ_SHIFT + SOFTIRQ_BITS)
#define PREEMPT_BITS    8
#define SOFTIRQ_BITS    8

/*
 * CPU hotplug.
 */

struct notifier_block {
	int (*notifier_call)(struct notifier_block *, unsigned long, void *);
	struct notifier_block *next;
	int priority;
};

#define CPU_ONLINE		0x0002 /* CPU (unsigned)v is up */
#define CPU_UP_PREPARE		0x0003 /* CPU (unsigned)v coming up */
#define CPU_UP_CANCELED		0x0004 /* CPU (unsigned)v NOT coming up */
#define CPU_DOWN_PREPARE	0x0005 /* CPU (unsigned)v going down */
#define CPU_DOWN_FAILED		0x0006 /* CPU (unsigned)v NOT going down */
#define CPU_DEAD		0x0007 /* CPU (unsigned)v dead */
#define CPU_DYING		0x0008 /* CPU (unsigned)v not running any task,
				        * not handling interrupts, soon dead */
#define CPU_POST_DEAD		0x0009 /* CPU (unsigned)v dead, cpu_hotplug
					* lock is dropped */

/* Used for CPU hotplug events occuring while tasks are frozen due to a suspend
 * operation in progress
 */
#define CPU_TASKS_FROZEN	0x0010

#define CPU_ONLINE_FROZEN	(CPU_ONLINE | CPU_TASKS_FROZEN)
#define CPU_UP_PREPARE_FROZEN	(CPU_UP_PREPARE | CPU_TASKS_FROZEN)
#define CPU_UP_CANCELED_FROZEN	(CPU_UP_CANCELED | CPU_TASKS_FROZEN)
#define CPU_DOWN_PREPARE_FROZEN	(CPU_DOWN_PREPARE | CPU_TASKS_FROZEN)
#define CPU_DOWN_FAILED_FROZEN	(CPU_DOWN_FAILED | CPU_TASKS_FROZEN)
#define CPU_DEAD_FROZEN		(CPU_DEAD | CPU_TASKS_FROZEN)
#define CPU_DYING_FROZEN	(CPU_DYING | CPU_TASKS_FROZEN)

/* Hibernation and suspend events */
#define PM_HIBERNATION_PREPARE	0x0001 /* Going to hibernate */
#define PM_POST_HIBERNATION	0x0002 /* Hibernation finished */
#define PM_SUSPEND_PREPARE	0x0003 /* Going to suspend the system */
#define PM_POST_SUSPEND		0x0004 /* Suspend finished */
#define PM_RESTORE_PREPARE	0x0005 /* Going to restore a saved image */
#define PM_POST_RESTORE		0x0006 /* Restore failed */

#define NOTIFY_DONE		0x0000		/* Don't care */
#define NOTIFY_OK		0x0001		/* Suits me */
#define NOTIFY_STOP_MASK	0x8000		/* Don't call further */
#define NOTIFY_BAD		(NOTIFY_STOP_MASK|0x0002)
						/* Bad/Veto action */
/*
 * Clean way to return from the notifier and stop further calls.
 */
#define NOTIFY_STOP		(NOTIFY_OK|NOTIFY_STOP_MASK)

/*
 * Bug checks.
 */

#define BUG_ON(c) do { if (c) abort(); } while (0)

/*
 * Initialization -- Must be called before calling any primitives.
 */

static __inline__ void smp_init(void)
{
	int i;

	spin_lock_init(&__thread_id_map_mutex);
	__thread_id_map[0] = pthread_self();
	for (i = 1; i < NR_THREADS; i++)
		__thread_id_map[i] = __THREAD_ID_MAP_EMPTY;
	init_per_thread(smp_processor_id, 0);
	if (pthread_key_create(&thread_id_key, NULL) != 0) {
		perror("pthread_key_create");
		exit(EXIT_FAILURE);
	}
}
