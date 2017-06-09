ARCH_INDEPENDENT = locked_list
ARCH_DEPENDENT = xchglock
PROGS = $(ARCH_INDEPENDENT) $(ARCH_DEPENDENT)

top := ..
include $(top)/depends.mk

ifeq ($(strip $(target)),)
all: $(ARCH_INDEPENDENT)
	@echo "### $(ARCH_DEPENDENT) in locking/ can't be built on arch: '$(arch)'."
else
all: $(PROGS)
endif

include $(top)/recipes.mk

locked_list: locked_list.c ../api.h
	cc -g -Wall -o locked_list locked_list.c

xchglock: xchglock.c ../api.h
	cc -g -Wall -o xchglock xchglock.c -lpthread

clean:
	rm -f $(PROGS)
