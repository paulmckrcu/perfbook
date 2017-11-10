LITMUS := $(wildcard *.litmus)
LITMUS_OUT = $(addsuffix .out,$(LITMUS))
CCOPTS = -fomit-frame-pointer -O2
CCOPTS += -I$(shell pwd)
CUSTOM_HEADER := $(wildcard *.h)

.PHONY: all clean cross-x86 cross-ppc cross-arm cross

all: $(LITMUS_OUT)

%.litmus.out: %.litmus $(CUSTOM_HEADER)
	litmus7 -r 1000 -carch X86 -ccopts "$(CCOPTS)" $< > $@ 2>&1

cross-x86: TARGET = X86
cross-x86: cross

cross-ppc: TARGET = PPC
cross-ppc: cross

cross-arm: TARGET = ARM
cross-arm: cross

cross:
	echo > @all
	for l in $(LITMUS); do \
	    echo $$l >> @all; \
	done
	mkdir -p $(TARGET)
	litmus7 -r 1000 -carch $(TARGET) -o $(TARGET) @all
	cp $(CUSTOM_HEADER) $(TARGET)

clean:
	rm -f *.out
	rm -f @all
