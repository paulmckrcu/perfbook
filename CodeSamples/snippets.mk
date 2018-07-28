FCVSNIPPETS = api-pthreads/api-pthreads@waitall.fcv \
	toolsoftrade/forkjoinvar@main.fcv \
	toolsoftrade/pcreate@mythread.fcv


.PHONY: all clean

all: $(FCVSNIPPETS)

api-pthreads/api-pthreads@waitall.fcv: api-pthreads/api-pthreads.h
toolsoftrade/forkjoinvar@main.fcv: toolsoftrade/forkjoinvar.c
toolsoftrade/pcreate@mythread.fcv: toolsoftrade/pcreate.c

$(FCVSNIPPETS):
	@echo "$< --> $@"
	../utilities/fcvextract.pl $< $(subst @,:,$(basename $(notdir $@))) > $@

clean:
	rm -f $(FCVSNIPPETS)
