#define NUMPROCS 2

byte counter = 0;
byte progress[NUMPROCS];

//\begin{snippet}[labelbase=ln:formal:promela:atomicincrement:incrementer,commandchars=\\\@\$]
proctype incrementer(byte me)
{
	int temp;

	atomic {
		temp = counter;
		counter = temp + 1;
	}
	progress[me] = 1;
}
//\end{snippet}

init {
	int i = 0;
	int sum = 0;

	atomic {
		i = 0;
		do
		:: i < NUMPROCS ->
			progress[i] = 0;
			run incrementer(i);
			i++
		:: i >= NUMPROCS -> break
		od;
	}
	atomic {
		i = 0;
		sum = 0;
		do
		:: i < NUMPROCS ->
			sum = sum + progress[i];
			i++
		:: i >= NUMPROCS -> break
		od;
		assert(sum < NUMPROCS || counter == NUMPROCS)
	}
}
