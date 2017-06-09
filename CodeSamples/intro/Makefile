ARCH_INDEPENDENT = initraceperf lockinc nakedinc perthreadinc threadcreate
ARCH_DEPENDENT = initrace
PROGS = $(ARCH_DEPENDENT) $(ARCH_INDEPENDENT)

top := ..
include $(top)/depends.mk

ifeq ($(strip $(target)),)
all: $(ARCH_INDEPENDENT)
	@echo "### $(ARCH_DEPENDENT) in intro/ can't be built on arch: '$(arch)'."
else
all: $(PROGS)
endif

include $(top)/recipes.mk

initrace: initrace.c ../api.h
	cc -g -Wall -o initrace initrace.c -lpthread

initraceperf: initraceperf.c ../api.h
	cc -g -Wall -o initraceperf initraceperf.c -lpthread

lockinc: lockinc.c ../api.h
	cc -g -Wall -o lockinc lockinc.c -lpthread

nakedinc: nakedinc.c ../api.h
	cc -g -Wall -o nakedinc nakedinc.c -lpthread

perthreadinc: perthreadinc.c ../api.h
	cc -g -Wall -o perthreadinc perthreadinc.c -lpthread

threadcreate: threadcreate.c ../api.h
	cc -g -Wall -o threadcreate threadcreate.c -lpthread

clean:
	rm -f $(PROGS)
