//\begin{snippet}[labelbase=ln:formal:promela:lock:spin,commandchars=\\\@\$]
#include "lock.h"

#define N_LOCKERS 3			//\lnlbl{nlockers}

bit mutex = 0;				//\lnlbl{mutex}
bit havelock[N_LOCKERS];		//\lnlbl{array}
int sum;				//\lnlbl{sum}

proctype locker(byte me)		//\lnlbl{locker:b}
{
	do
	:: 1 ->
		spin_lock(mutex);	//\lnlbl{locker:lock}
		havelock[me] = 1;	//\lnlbl{locker:claim}
		havelock[me] = 0;	//\lnlbl{locker:unclaim}
		spin_unlock(mutex)	//\lnlbl{locker:unlock}
	od
}					//\lnlbl{locker:e}

init {					//\lnlbl{init:b}
	int i = 0;
	int j;

end:	do 
	:: i < N_LOCKERS ->
		havelock[i] = 0;	//\lnlbl{init:array}
		run locker(i);		//\lnlbl{init:start}
		i++			//\lnlbl{init:next}
	:: i >= N_LOCKERS ->		//\lnlbl{init:chkassert}
		sum = 0;		//\lnlbl{init:sum}
		j = 0;			//\lnlbl{init:j}
		atomic {		//\lnlbl{init:atm:b}
			do
			:: j < N_LOCKERS ->
				sum = sum + havelock[j];
				j = j + 1
			:: j >= N_LOCKERS ->
				break
			od
		}			//\lnlbl{init:atm:e}
		assert(sum <= 1);	//\lnlbl{init:assert}
		break			//\lnlbl{init:break}
	od
}					//\lnlbl{init:e}
//\end{snippet}
