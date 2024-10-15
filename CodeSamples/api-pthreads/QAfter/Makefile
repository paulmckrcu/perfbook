CFLAGS=-g

all: time timecost timelocked timeskew

time: time.o
	cc -g -o time time.o -lpthread

timecost: timecost.o
	cc -g -o timecost timecost.o

timelocked: timelocked.o
	cc -g -o timelocked timelocked.o -lpthread

timeskew: timeskew.o
	cc -g -o timeskew timeskew.o
