
CFLAGS=-Wall -O2 -g
LDFLAGS=-lpthread

#debug
#CFLAGS=-Wall -g
#CFLAGS+=-DDEBUG_FULL_MB

SRC_DEP=`echo $^ | sed 's/[^ ]*.h//g'`

all: test_urcu test_urcu_timing test_rwlock_timing test_urcu_yield urcu-asm.S \
	urcu-asm.o

test_urcu: urcu.o test_urcu.c urcu.h
	$(CC) ${CFLAGS} -o $@ $(SRC_DEP) $(LDFLAGS)

test_urcu_yield: urcu-yield.o test_urcu.c urcu.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} -o $@ $(SRC_DEP) $(LDFLAGS)

test_urcu_timing: urcu.o test_urcu_timing.c urcu.h
	$(CC) ${CFLAGS} -o $@ $(SRC_DEP) $(LDFLAGS)

test_rwlock_timing: urcu.o test_rwlock_timing.c urcu.h
	$(CC) ${CFLAGS} -o $@ $(SRC_DEP) $(LDFLAGS)

urcu.o: urcu.c urcu.h
	$(CC) ${CFLAGS} -c -o $@ $(SRC_DEP) $(LDFLAGS)

urcu-yield.o: urcu.c urcu.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} -c -o $@ $(SRC_DEP) $(LDFLAGS)

urcu-asm.S: urcu-asm.c urcu.h
	$(CC) ${CFLAGS} -S -o $@ $(SRC_DEP)

urcu-asm.o: urcu-asm.c urcu.h
	$(CC) ${CFLAGS} -c -o $@ $(SRC_DEP)

.PHONY: clean

clean:
	rm -f *.o test_urcu test_urcu_timing test_rwlock_timing urcu-asm.S \
		test_urcu_yield
