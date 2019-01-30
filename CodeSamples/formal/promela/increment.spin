//\begin{snippet}[labelbase=ln:formal:promela:increment:whole,commandchars=\\\@\$]
#define NUMPROCS 2		//\lnlbl{nprocs}

byte counter = 0;		//\lnlbl{count}
byte progress[NUMPROCS];	//\lnlbl{prog}

proctype incrementer(byte me)	//\lnlbl{proc:b}
{
	int temp;

	temp = counter;		//\lnlbl{incr:b}
	counter = temp + 1;	//\lnlbl{incr:e}
	progress[me] = 1;	//\lnlbl{setprog}
}				//\lnlbl{proc:e}

init {				//\lnlbl{init:b}
	int i = 0;
	int sum = 0;

	atomic {		//\lnlbl{doinit:b}
		i = 0;
		do		//\lnlbl{dood1:b}
		:: i < NUMPROCS ->	//\lnlbl{block1:b}
			progress[i] = 0;
			run incrementer(i);
			i++;		//\lnlbl{block1:e}
		:: i >= NUMPROCS -> break;	//\lnlbl{block2}
		od;		//\lnlbl{dood1:e}
	}			//\lnlbl{doinit:e}
	atomic {		//\lnlbl{assert:b}
		i = 0;
		sum = 0;
		do		//\lnlbl{dood2:b}
		:: i < NUMPROCS ->
			sum = sum + progress[i];
			i++
		:: i >= NUMPROCS -> break;
		od;		//\lnlbl{dood2:e}
		assert(sum < NUMPROCS || counter == NUMPROCS);	//\lnlbl{assert}
	}			//\lnlbl{assert:e}
}				//\lnlbl{init:e}
//\end{snippet}
