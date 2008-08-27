CFLAGS=-g

all: time timelocked

time: time.o
	cc -g -o time time.o -lpthread

timelocked: timelocked.o
	cc -g -o timelocked timelocked.o -lpthread
