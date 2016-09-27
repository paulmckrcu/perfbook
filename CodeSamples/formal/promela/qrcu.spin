#include "lock.h"

#define N_QRCU_READERS 2
#define N_QRCU_UPDATERS 2

bit idx = 0;
byte ctr[2];
byte readerprogress[N_QRCU_READERS];
bit mutex = 0;

proctype qrcu_reader(byte me)
{
	int myidx;

	do
	:: 1 ->
		myidx = idx;
		atomic {
			if
			:: ctr[myidx] > 0 ->
				ctr[myidx]++;
				break
			:: else -> skip
			fi
		}
	od;
	readerprogress[me] = 1;
	readerprogress[me] = 2;
	atomic { ctr[myidx]-- }
}

#define sum_unordered \
	atomic { \
		if \
		:: 1 -> \
			sum = ctr[0]; \
			i = 1; \
		:: 1 -> \
			sum = ctr[1]; \
			i = 0; \
		fi; \
	} \
	sum = sum + ctr[i]

proctype qrcu_updater(byte me)
{
	int i;
	byte readerstart[N_QRCU_READERS];
	int sum;

	do
	:: 1 ->

		/* Snapshot reader state. */

		atomic {
			i = 0;
			do
			:: i < N_QRCU_READERS ->
				readerstart[i] = readerprogress[i];
				i++
			:: i >= N_QRCU_READERS ->
				break
			od
		}

		sum_unordered;
		if
		:: sum <= 1 -> sum_unordered
		:: else -> skip
		fi;
		if
		:: sum > 1 ->
			spin_lock(mutex);
			atomic { ctr[!idx]++ }
			idx = !idx;
			atomic { ctr[!idx]-- }
			do
			:: ctr[!idx] > 0 -> skip
			:: ctr[!idx] == 0 -> break
			od;
			spin_unlock(mutex);
		:: else -> skip
		fi;

		/* Verify reader progress. */

		atomic {
			i = 0;
			sum = 0;
			do
			:: i < N_QRCU_READERS ->
				sum = sum + (readerstart[i] == 1 &&
					     readerprogress[i] == 1);
				i++
			:: i >= N_QRCU_READERS ->
				assert(sum == 0);
				break
			od
		}
	od
}

init {
	int i;

	atomic {
		ctr[idx] = 1;
		ctr[!idx] = 0;
		i = 0;
		do
		:: i < N_QRCU_READERS ->
			readerprogress[i] = 0;
			run qrcu_reader(i);
			i++
		:: i >= N_QRCU_READERS -> break
		od;
		i = 0;
		do
		:: i < N_QRCU_UPDATERS ->
			run qrcu_updater(i);
			i++
		:: i >= N_QRCU_UPDATERS -> break
		od
	}
}
