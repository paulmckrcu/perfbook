CFLAGS=-g

all: time timelocked timeskew

time: time.o
	cc -g -o time time.o -lpthread

timelocked: timelocked.o
	cc -g -o timelocked timelocked.o -lpthread

timeskew: timeskew.o
	cc -g -o timeskew timeskew.o
