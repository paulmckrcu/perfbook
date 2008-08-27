/*
 * rcutorture.c: simple user-level performance/stress test of RCU.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
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
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

/*
 * Test variables.
 */

DEFINE_PER_THREAD(long long, n_reads_pt);

long long n_reads = 0LL;
long n_updates = 0L;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag = GOFLAG_INIT;

#define RCU_READ_RUN 1000

#ifdef RCU_READ_NESTABLE
#define rcu_read_lock_nest() rcu_read_lock()
#define rcu_read_unlock_nest() rcu_read_unlock()
#else /* #ifdef RCU_READ_NESTABLE */
#define rcu_read_lock_nest()
#define rcu_read_unlock_nest()
#endif /* #else #ifdef RCU_READ_NESTABLE */

#ifndef mark_rcu_quiescent_state
#define mark_rcu_quiescent_state() do ; while (0)
#endif /* #ifdef mark_rcu_quiescent_state */

#ifndef put_thread_offline
#define put_thread_offline()		do ; while (0)
#define put_thread_online()		do ; while (0)
#define put_thread_online_delay()	do ; while (0)
#else /* #ifndef put_thread_offline */
#define put_thread_online_delay()	synchronize_rcu()
#endif /* #else #ifndef put_thread_offline */

/*
 * Performance test.
 */

void *rcu_read_perf_test(void *arg)
{
	int i;

	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 10);
	while (goflag == GOFLAG_RUN) {
		for (i = 0; i < RCU_READ_RUN; i++) {
			rcu_read_lock();
			rcu_read_lock_nest();
			rcu_read_unlock_nest();
			rcu_read_unlock();
		}
		__get_thread_var(n_reads_pt) += RCU_READ_RUN;
		mark_rcu_quiescent_state();
	}
	put_thread_offline();

	return (NULL);
}

void *rcu_update_perf_test(void *arg)
{
	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 10);
	while (goflag == GOFLAG_RUN) {
		synchronize_rcu();
		n_updates++;
	}
}

void perftest(int nreaders)
{
	int i;
	int t;

	init_per_thread(n_reads_pt, 0LL);
	for (i = 0; i < nreaders; i++)
		create_thread(rcu_read_perf_test, NULL);
	create_thread(rcu_update_perf_test, NULL);
	smp_mb();
	goflag = GOFLAG_RUN;
	smp_mb();
	sleep(1);
	smp_mb();
	goflag = GOFLAG_STOP;
	smp_mb();
	wait_all_threads();
	for_each_thread(t)
		n_reads += per_thread(n_reads_pt, t);
	printf("n_reads: %lld  n_updates: %ld\n", n_reads, n_updates);
	exit(0);
}

/*
 * Stress test.
 */

#define RCU_STRESS_PIPE_LEN 10

struct rcu_stress {
	int pipe_count;
	int mbtest;
};

struct rcu_stress rcu_stress_array[RCU_STRESS_PIPE_LEN] = { 0 };
struct rcu_stress *rcu_stress_current;
int rcu_stress_idx = 0;

int n_mberror = 0;
DEFINE_PER_THREAD(long long [RCU_STRESS_PIPE_LEN + 1], rcu_stress_count);

int garbage = 0;

void *rcu_read_stress_test(void *arg)
{
	int i;
	int itercnt = 0;
	struct rcu_stress *p;
	int pc;

	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 10);
	while (goflag == GOFLAG_RUN) {
		rcu_read_lock();
		p = rcu_dereference(rcu_stress_current);
		if (p->mbtest == 0)
			n_mberror++;
		rcu_read_lock_nest();
		for (i = 0; i < 100; i++)
			garbage++;
		rcu_read_unlock_nest();
		pc = p->pipe_count;
		rcu_read_unlock();
		if ((pc > RCU_STRESS_PIPE_LEN) || (pc < 0))
			pc = RCU_STRESS_PIPE_LEN;
		__get_thread_var(rcu_stress_count)[pc]++;
		__get_thread_var(n_reads_pt)++;
		mark_rcu_quiescent_state();
		if ((++itercnt % 0x1000) == 0) {
			put_thread_offline();
			put_thread_online_delay();
			put_thread_online();
		}
	}
	put_thread_offline();

	return (NULL);
}

void *rcu_update_stress_test(void *arg)
{
	int i;
	struct rcu_stress *p;

	while (goflag == GOFLAG_INIT)
		poll(NULL, 0, 10);
	while (goflag == GOFLAG_RUN) {
		i = rcu_stress_idx + 1;
		if (i >= RCU_STRESS_PIPE_LEN)
			i = 0;
		p = &rcu_stress_array[i];
		p->mbtest = 0;
		smp_mb();
		p->pipe_count = 0;
		p->mbtest = 1;
		rcu_assign_pointer(rcu_stress_current, p);
		rcu_stress_idx = i;
		for (i = 0; i < RCU_STRESS_PIPE_LEN; i++)
			if (i != rcu_stress_idx)
				rcu_stress_array[i].pipe_count++;
		synchronize_rcu();
		n_updates++;
	}
}

void stresstest(int nreaders)
{
	int i;
	int t;
	long long *p;
	long long sum;

	init_per_thread(n_reads_pt, 0LL);
	for_each_thread(t) {
		p = &per_thread(rcu_stress_count,t)[0];
		for (i = 0; i <= RCU_STRESS_PIPE_LEN; i++)
			p[i] = 0LL;
	}
	rcu_stress_current = &rcu_stress_array[0];
	rcu_stress_current->pipe_count = 0;
	rcu_stress_current->mbtest = 1;
	for (i = 0; i < nreaders; i++)
		create_thread(rcu_read_stress_test, NULL);
	create_thread(rcu_update_stress_test, NULL);
	smp_mb();
	goflag = GOFLAG_RUN;
	smp_mb();
	sleep(10);
	smp_mb();
	goflag = GOFLAG_STOP;
	smp_mb();
	wait_all_threads();
	for_each_thread(t)
		n_reads += per_thread(n_reads_pt, t);
	printf("n_reads: %lld  n_updates: %ld  n_mberror: %ld\n",
	       n_reads, n_updates, n_mberror);
	printf("rcu_stress_count:");
	for (i = 0; i <= RCU_STRESS_PIPE_LEN; i++) {
		sum = 0LL;
		for_each_thread(t) {
			sum += per_thread(rcu_stress_count, t)[i];
		}
		printf(" %lld", sum);
	}
	printf("\n");
	exit(0);
}

/*
 * Mainprogram.
 */

void usage(int argc, char *argv[])
{
	fprintf(stderr, "Usage: %s [nreaders [ perf | stress ] ]\n", argv[0]);
	exit(-1);
}

int main(int argc, char *argv[])
{
	int nreaders = 1;

	smp_init();
	rcu_init();

	if (argc > 1) {
		nreaders = strtoul(argv[1], NULL, 0);
		if (argc == 2)
			perftest(nreaders);
		if (strcmp(argv[2], "perf") == 0)
			perftest(nreaders);
		else if (strcmp(argv[2], "stress") == 0)
			stresstest(nreaders);
		usage(argc, argv);
	}
	perftest(1);
}
