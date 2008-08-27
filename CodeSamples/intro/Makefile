all: lockinc nakedinc perthreadinc threadcreate

lockinc: lockinc.c ../api.h
	cc -g -o lockinc lockinc.c -lpthread

nakedinc: nakedinc.c ../api.h
	cc -g -o nakedinc nakedinc.c -lpthread

perthreadinc: perthreadinc.c ../api.h
	cc -g -o perthreadinc perthreadinc.c -lpthread

threadcreate: threadcreate.c ../api.h
	cc -g -o threadcreate threadcreate.c -lpthread
