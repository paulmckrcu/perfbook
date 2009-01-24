all: smpalloc lockdeq

smpalloc: smpalloc.c ../api.h
	cc -g -o smpalloc -DTEST smpalloc.c -lpthread

lockdeq: lockdeq.c ../api.h
	cc -g -o lockdeq -DTEST lockdeq.c -lpthread
