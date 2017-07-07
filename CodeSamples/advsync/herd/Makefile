LITMUS := $(wildcard *.litmus)
LITMUS_OUT = $(addsuffix .out,$(LITMUS))
CCOPTS = -fomit-frame-pointer -O2
CCOPTS += -I$(shell pwd)

.PHONY: all clean

all: $(LITMUS_OUT)

%.litmus.out: %.litmus
	litmus7 -r 1000 -carch X86 -ccopts "$(CCOPTS)" $< > $@ 2>&1

clean:
	rm -f *.out
