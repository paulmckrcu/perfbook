//\begin{snippet}[labelbase=ln:formal:promela:qrcu:gvar,commandchars=\\\{\}]
#include "lock.h"

#define N_QRCU_READERS 2
#define N_QRCU_UPDATERS 2

bit idx = 0;
byte ctr[2];
byte readerprogress[N_QRCU_READERS];
bit mutex = 0;
//\end{snippet}

//\begin{snippet}[labelbase=ln:formal:promela:qrcu:reader,commandchars=\\\@\$]
proctype qrcu_reader(byte me)
{
	int myidx;

	do				//\lnlbl{do}
	:: 1 ->				//\lnlbl{one}
		myidx = idx;		//\lnlbl{curidx}
		atomic {		//\lnlbl{atm:b}
			if
			:: ctr[myidx] > 0 ->
				ctr[myidx]++;
				break
			:: else -> skip
			fi
		}			//\lnlbl{atm:e}
	od;				//\lnlbl{od}
	readerprogress[me] = 1;		//\lnlbl{cs:entry}
	readerprogress[me] = 2;		//\lnlbl{cs:exit}
	atomic { ctr[myidx]-- }		//\lnlbl{atm:dec}
}
//\end{snippet}

//\begin{snippet}[labelbase=ln:formal:promela:qrcu:sum_unordered,commandchars=\!\@\$]
#ifndef FCV_SNIPPET
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
#else /* #ifndef FCV_SNIPPET */
#define sum_unordered \
	atomic { /* \lnlbl{fetch:b} */\
		do /* \lnlbl{do} */\
		:: 1 -> /* \lnlbl{g1} */\
			sum = ctr[0]; \
			i = 1; \
			break \
		:: 1 -> /* \lnlbl{g2} */\
			sum = ctr[1]; \
			i = 0; \
			break \
		od; /* \lnlbl{od} */\
	} /* \lnlbl{fetch:e} */\
	sum = sum + ctr[i] /* \lnlbl{sum_other} */
#endif /* #ifndef FCV_SNIPPET */
//\end{snippet}

//\begin{snippet}[labelbase=ln:formal:promela:qrcu:updater,keepcomment=yes,commandchars=\\\@\$]
proctype qrcu_updater(byte me)
{
	int i;
	byte readerstart[N_QRCU_READERS];
	int sum;

	do					//\lnlbl{do}
	:: 1 ->

		/* Snapshot reader state. */

		atomic {			//\lnlbl{atm1:b}
			i = 0;
			do
			:: i < N_QRCU_READERS ->
				readerstart[i] = readerprogress[i];
				i++
			:: i >= N_QRCU_READERS ->
				break
			od
		}				//\lnlbl{atm1:e}

		sum_unordered;			//\lnlbl{sum_unord}
		if				//\lnlbl{reinvoke:b}
		:: sum <= 1 -> sum_unordered
		:: else -> skip
		fi;				//\lnlbl{reinvoke:e}
		if				//\lnlbl{slow:b}
		:: sum > 1 ->
			spin_lock(mutex);	//\lnlbl{acq}
			atomic { ctr[!idx]++ }	//\lnlbl{flip_idx:b}
			idx = !idx;
			atomic { ctr[!idx]-- }	//\lnlbl{flip_idx:e}
			do			//\lnlbl{wait:b}
			:: ctr[!idx] > 0 -> skip
			:: ctr[!idx] == 0 -> break
			od;			//\lnlbl{wait:e}
			spin_unlock(mutex);	//\lnlbl{rel}
		:: else -> skip
		fi;				//\lnlbl{slow:e}

		/* Verify reader progress. */

		atomic {			//\lnlbl{atm2:b}
			i = 0;
			sum = 0;
			do
			:: i < N_QRCU_READERS ->
				sum = sum + (readerstart[i] == 1 &&
				             readerprogress[i] == 1);
				i++
			:: i >= N_QRCU_READERS ->
				assert(sum == 0);	//\lnlbl{assert}
				break
			od
		}				//\lnlbl{atm2:e}
	od					//\lnlbl{od}
}
//\end{snippet}

//\begin{snippet}[labelbase=ln:formal:promela:qrcu:init,commandchars=\\\@\$]
init {
	int i;

	atomic {
		ctr[idx] = 1;			//\lnlbl{i_ctr:b}
		ctr[!idx] = 0;			//\lnlbl{i_ctr:e}
		i = 0;				//\lnlbl{spn_r:b}
		do
		:: i < N_QRCU_READERS ->
			readerprogress[i] = 0;
			run qrcu_reader(i);
			i++
		:: i >= N_QRCU_READERS -> break
		od;				//\lnlbl{spn_r:e}
		i = 0;				//\lnlbl{spn_u:b}
		do
		:: i < N_QRCU_UPDATERS ->
			run qrcu_updater(i);
			i++
		:: i >= N_QRCU_UPDATERS -> break
		od				//\lnlbl{spn_u:e}
	}
}
//\end{snippet}
