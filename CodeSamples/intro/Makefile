PROGS = initrace initraceperf lockinc nakedinc perthreadinc threadcreate

all: $(PROGS)

top := ..
include $(top)/depends.mk

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
