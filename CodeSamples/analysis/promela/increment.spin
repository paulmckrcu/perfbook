#define NUMPROCS 3

byte counter = 0;
byte progress[NUMPROCS];

proctype incrementer(byte me)
{
	int temp;

	temp = counter;
	counter = temp + 1;
	progress[me] = 1;
}

init {
	int i = 0;
	int sum = 0;

	atomic {
		i = 0;
		do
		:: i < NUMPROCS ->
			progress[i] = 0;
			run incrementer(i);
			i++;
		:: i >= NUMPROCS -> break;
		od;
	}
	atomic {
		i = 0;
		sum = 0;
		do
		:: i < NUMPROCS ->
			sum = sum + progress[i];
			i++
		:: i >= NUMPROCS -> break;
		od;
		assert(sum < NUMPROCS || counter == NUMPROCS);
	}
}
