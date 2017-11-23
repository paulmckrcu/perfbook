# SPDX-License-Identifier: GPL-2.0
#
# Default target: Transform litmus tests in ../litmus to herd7 compatible format
#         (remove 2nd {})
#
# run-herd7: Examine transformed litmus tests by herd7 with LKMM
#
# cross-klitmus7: Cross-compile transformed litmus tests with klitmus7
#
# run-herd7-bench: Run benchmark tests of herd7 itself
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
HERD_BENCH        := $(wildcard C-SB+l-*.litmus)
HERD_BENCH_LONG   := $(wildcard C-SB+l-o-o-u+l-o-o-u+l-o-o-u+l-o-o-u+l-o-o-u-*.litmus)
HERD_BENCH_SHORT  := $(filter-out $(HERD_BENCH_LONG),$(HERD_BENCH))
HERD_BENCH_OUT    := $(addsuffix .out,$(HERD_BENCH_SHORT))

.PHONY: all clean litmus2herd run-herd7 run-herd7-bench cross-klitmus

all: litmus2herd

litmus2herd: $(LITMUS7_HERD_TEST)

$(LITMUS7_HERD_TEST): %.herd: ../litmus/%
	sh ./litmus2herd.sh $< $@

run-herd7: $(LITMUS7_HERD_OUT)

run-herd7-bench: $(HERD_BENCH_OUT)

$(LKMM_LIST):
	@echo "#####################################################"
	@echo "### Please prepare Linux Kernel Memory Model.     ###"
	@echo "### You can get it at the git archive:            ###"
	@echo "###   https://github.com/aparri/memory-model.git  ###"
	@echo "###                                               ###"
	@echo "### Refer to comment in Makefile for more info.   ###"
	@echo "#####################################################"
	@exit 1

$(LITMUS7_HERD_OUT) $(HERD_BENCH_OUT): $(LKMM_LIST)

$(LITMUS7_HERD_OUT): %.out: %.herd
	cd $(LKMM_DIR); herd7 -conf linux-kernel.cfg $(HERD_DIR)/$< > $(HERD_DIR)/$@

$(HERD_BENCH_OUT): %.out: %
	cd $(LKMM_DIR); herd7 -conf linux-kernel.cfg $(HERD_DIR)/$< > $(HERD_DIR)/$@

cross-klitmus: klitmus.tar

klitmus.tar: litmus2herd
	mkdir -p klitmus
	klitmus7 -o klitmus $(LITMUS7_HERD_TEST)
	tar cf klitmus.tar ./klitmus

clean:
	rm -f *.out *.herd
	rm -rf klitmus
	rm -f klitmus.tar
