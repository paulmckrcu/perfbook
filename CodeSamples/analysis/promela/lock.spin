#include "lock.h"

#define N_LOCKERS 3

bit mutex = 0;
bit havelock[N_LOCKERS];
int sum;

proctype locker(byte me)
{
	do
	:: 1 ->
		spin_lock(mutex);
		havelock[me] = 1;
		havelock[me] = 0;
		spin_unlock(mutex)
	od
}

init {
	int i = 0;
	int j;

end:	do 
	:: i < N_LOCKERS ->
		havelock[i] = 0;
		run locker(i);
		i++
	:: i >= N_LOCKERS ->
		sum = 0;
		j = 0;
		atomic {
			do
			:: j < N_LOCKERS ->
				sum = sum + havelock[j];
				j = j + 1
			:: j >= N_LOCKERS ->
				break
			od
		}
		assert(sum <= 1);
		break
	od
}
