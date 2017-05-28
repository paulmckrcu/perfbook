PROGS = locked_list xchglock

all: $(PROGS)

top := ..
include $(top)/depends.mk

locked_list: locked_list.c ../api.h
	cc -g -Wall -o locked_list locked_list.c

xchglock: xchglock.c ../api.h
	cc -g -Wall -o xchglock xchglock.c -lpthread

clean:
	rm -f $(PROGS)
