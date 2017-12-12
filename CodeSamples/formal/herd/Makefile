# SPDX-License-Identifier: GPL-2.0
#
# Default target: Transform litmus tests in ../litmus to herd7 compatible format
#         (remove 2nd {})
#
# run-herd7:       Examine transformed litmus tests by herd7 with LKMM
# cross-klitmus7:  Cross-compile transformed litmus tests by klitmus7
# run-absperf:     Run memory model benchmark tests of absperf
# run-absperf-all: Run all absperf tests (including those take quite a while)
#
# Warning: absperf tests take more than 1 hour by default.
#
# Note: Parameters TIMEOUT and ITER in absperf.sh can be overridden by
#       options to "make".  E.g.:
#
#       $ make TIMEOUT=1m ITER=3 run-absperf
#
# Note: There need to be a symbolic link "memory-model" under
#       CodeSamples/formal/herd for herd7 to work.
#       The memory model is available at the git archive:
#           https://github.com/aparri/memory-model.git.
#       Make sure the symbolic link points to the actual directory.
#       Alternatively, you can copy the files listed in LKMM_FILES to
#       a subdirectory "memory-model".
#
#       klitmus7 doesn't require the memory model.
#
# Copyright (C) Akira Yokosawa, 2017
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

LKMM_DIR     := memory-model
LKMM_FILES   := linux-kernel.bell linux-kernel.cat linux-kernel.cfg \
		linux-kernel.def linux-kernel-hardware.cat lock.cat
LKMM_LIST    := $(addprefix $(LKMM_DIR)/,$(LKMM_FILES))
HERD_DIR     := $(shell pwd)
HERD7_CMD    := $(shell which herd7)
KLITMUS7_CMD := $(shell which klitmus7)
LITMUS7_TEST := $(notdir $(wildcard ../litmus/*.litmus))
LITMUS7_HERD_TEST := $(addsuffix .herd,$(LITMUS7_TEST))
LITMUS7_HERD_OUT  := $(addsuffix .out,$(LITMUS7_TEST))
TIMEOUT = 15m
ITER    = 10
ABSPERF_TEST   := $(wildcard C-SB+l-*.litmus)
ABSPERF_LONG   := $(wildcard C-SB+l-o-o-u+l-o-o-u+l-o-o-u+l-o-o-u+l-o-o-u-*.litmus)
ABSPERF_SHORT  := $(filter-out $(ABSPERF_LONG),$(ABSPERF_TEST))
ABSPERF_OUT    = absperf.out absperf-all.out

.PHONY: all clean litmus2herd run-herd7 run-absperf run-absperf-all cross-klitmus
.PHONY: help

all: litmus2herd

litmus2herd: $(LITMUS7_HERD_TEST)

$(LITMUS7_HERD_TEST): %.herd: ../litmus/%
	sh ./litmus2herd.sh $< $@

run-herd7: $(LITMUS7_HERD_OUT)
run-absperf: absperf.out
run-absperf-all: absperf-all.out

$(LKMM_LIST):
	@echo "#####################################################"
	@echo "### Please prepare Linux Kernel Memory Model.     ###"
	@echo "### You can get it at the git archive:            ###"
	@echo "###   https://github.com/aparri/memory-model.git  ###"
	@echo "###                                               ###"
	@echo "### Refer to comment in Makefile for more info.   ###"
	@echo "#####################################################"
	@exit 1

$(LITMUS7_HERD_OUT) $(ABSPERF_OUT): $(LKMM_LIST)

$(LITMUS7_HERD_OUT): %.out: %.herd
	cd $(LKMM_DIR); herd7 -conf linux-kernel.cfg $(HERD_DIR)/$< > $(HERD_DIR)/$@

absperf.out: ABSPERF_LIST = $(ABSPERF_SHORT)
absperf.out: $(ABSPERF_SHORT)
absperf-all.out: ABSPERF_LIST = $(ABSPERF_TEST)
absperf-all.out: $(ABSPERF_TEST)
$(ABSPERF_OUT): export LC_ALL = C

$(ABSPERF_OUT):
	mkdir -p absperf
	rm -f absperf/*
	ln -s -r $(ABSPERF_LIST) absperf/
	cd $(LKMM_DIR); sh $(HERD_DIR)/absperf.sh $(HERD_DIR) $(TIMEOUT) $(ITER) >$(HERD_DIR)/$@.raw 2>&1
	cat $@.raw | sh ./absperf-reduce.sh | sed -e 's/^.*absperf\///' \
		| sort -r | tee $@

cross-klitmus: klitmus.tar

klitmus.tar: litmus2herd
	mkdir -p klitmus
	klitmus7 -o klitmus $(LITMUS7_HERD_TEST)
	tar cf klitmus.tar ./klitmus

help:
	@echo "Default target: Transform litmus tests in ../litmus to herd7 compatible format"
	@echo "        (remove 2nd {})"
	@echo
	@echo "Other targets:"
	@echo "    run-herd7:       Examine transformed litmus tests by herd7 with LKMM"
	@echo "    cross-klitmus7:  Cross-compile transformed litmus tests by klitmus7"
	@echo "    run-absperf:     Run memory model benchmark tests of absperf"
	@echo "    run-absperf-all: Run all absperf tests (including those take quite a while)"
	@echo
	@echo "Warning: absperf tests require more than 1 hour by default."
	@echo "    Refer to comment in Makefile for instructions to override default setting."

clean:
	rm -f *.out *.herd *.raw
	rm -rf klitmus absperf
	rm -f klitmus.tar
