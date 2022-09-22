# SPDX-License-Identifier: GPL-2.0-or-later
#
# Copyright (C) Akira Yokosawa, 2021
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

A2PING := $(shell which a2ping 2>/dev/null)

ifdef A2PING
  GS_950_OR_LATER := $(shell gs --version | grep -c -E "^(9\.[5-9]|10\.[0-9]).?")
  A2PING_277P := $(shell a2ping --help 2>&1 | grep -c "2.77p,")
  A2PING_283P := $(shell a2ping --help 2>&1 | grep -c "2.83p,")
  GS_953_OR_LATER := $(shell gs --version | grep -c -E "^(9\.5[3-9]|10\.[0-9]).?")
  ifeq ($(A2PING_277P),1)
    A2PING_GSCNFL = 1
  else
    ifeq ($(A2PING_283P),1)
      ifeq ($(GS_950_OR_LATER),1)
        A2PING_GSCNFL = 1
      else
        A2PING_GSCNFL = 0
      endif
    else
      A2PING_GSCNFL = 0
    endif
  endif
  ifeq ($(GS_953_OR_LATER),1)
    A2PING_GSCNFL = 2
  endif
endif

$(PDFTARGETS_OF_GNUPLOT_NEEDFIXFONTS): $(FIXANEPSFONTS) $(FIXFONTS)
$(PDFTARGETS_OF_GNUPLOT_NEEDFIXFONTS): %.pdf: %.eps
	@echo "$< --> $(suffix $@) (by a2ping)"
ifndef A2PING
	$(error $< --> $@: a2ping not found. Please install it)
endif
ifeq ($(A2PING_GSCNFL),1)
	$(error You need to update a2ping. See #7 in FAQ-BUILD.txt)
endif
	@cp $< $<i
	@sh $(FIXANEPSFONTS) $<i
	@a2ping --below --hires --bboxfrom=compute-gs $<i $@ > /dev/null 2>&1
	@rm -f $<i

$(PDFTARGETS_OF_TEX): %.pdf: %.eps
	@echo "$< --> $(suffix $@) (by a2ping)"
ifndef A2PING
	$(error $< --> $@: a2ping not found. Please install it)
endif
ifeq ($(A2PING_GSCNFL),1)
	$(error a2ping version conflict. See #7 in FAQ-BUILD.txt)
endif
ifeq ($(A2PING_GSCNFL),2)
	@a2ping --below --gsextra=-dALLOWPSTRANSPARENCY $< $(basename $@)__.pdf > /dev/null 2>&1
	@pdfcrop --hires $(basename $@)__.pdf $@ > /dev/null
	@rm -f $(basename $@)__.pdf
else
	@a2ping --below --hires --bboxfrom=compute-gs $< $@ > /dev/null 2>&1
endif

$(PDFTARGETS_OF_EPSORIG_NOFIXFONTS) $(PDFTARGETS_OF_EPSOTHER): %.pdf: %.eps
	@echo "$< --> $(suffix $@) (by a2ping)"
ifndef A2PING
	$(error $< --> $@: a2ping not found. Please install it)
endif
ifeq ($(A2PING_GSCNFL),1)
	$(error a2ping version conflict. See #7 in FAQ-BUILD.txt)
endif
	@a2ping --below --hires --bboxfrom=compute-gs $< $@ > /dev/null 2>&1
