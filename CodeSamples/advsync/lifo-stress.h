////////////////////////////////////////////////////////////////////////
//
// Stress-test code
//
// Also serves as a crude high-contention performance test.
//
// Copyright IBM Corporation, 2019
// Authors: Paul E. McKenney, IBM Linux Technology Center
//	Adapted from similar tests in "Is Parallel Programming Hard,
//	And, If So, What Can You Do About It?":
//	git://git.kernel.org/pub/scm/linux/kernel/git/paulmck/perfbook.git

#define N_PUSH 2
#define N_POP  2
#define N_ELEM (10 * 1000 * 1000L)

char s[N_PUSH * N_ELEM];
int goflag;

#ifndef list_empty
int list_empty(struct node_t *p)
{
	return p == NULL;
}
#endif

static void foo(struct node_t *p)
{
	(*p->val)++;
}

void *push_em(void *arg)
{
	long i;
	char *my_s = arg;

	rcu_register_thread();
	while (!READ_ONCE(goflag))
		continue;
	for (i = 0; i < N_ELEM; i++)
		list_push(&my_s[i]);
	rcu_unregister_thread();
	return NULL;
}

void *pop_em(void *arg)
{
	while (!READ_ONCE(goflag))
		continue;
	while (READ_ONCE(goflag) == 1)
		list_pop_all(foo);
	return NULL;
}

int main(int argc, char *argv[])
{
	long i;
	pthread_t tid[N_PUSH + N_POP];
	void *vp;

	for (i = 0; i < N_PUSH; i++)
		if (pthread_create(&tid[i], NULL, push_em, (void *)&s[N_ELEM * i])) {
			perror("pthread_create");
			exit(1);
		}
	for (i = 0; i < N_POP; i++)
		if (pthread_create(&tid[N_PUSH + i], NULL, pop_em, NULL)) {
			perror("pthread_create");
			exit(1);
		}
	WRITE_ONCE(goflag, 1);
	for (i = 0; i < N_PUSH; i++)
		if (pthread_join(tid[i], &vp) != 0) {
			perror("pthread_join");
			exit(1);
		}
	while (!list_empty(top))
		sleep(1);
	WRITE_ONCE(goflag, 2);
	for (i = 0; i < N_POP; i++)
		if (pthread_join(tid[N_PUSH + i], &vp) != 0) {
			perror("pthread_join");
			exit(1);
		}
	for (i = 0; i < N_PUSH * N_ELEM; i++)
		if (s[i] != 1) {
			fprintf(stderr, "Entry %ld left set\n", i);
			abort();
		}
}
