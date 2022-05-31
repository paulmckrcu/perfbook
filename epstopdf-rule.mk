# SPDX-License-Identifier: GPL-2.0-or-later
#
# Copyright (C) Akira Yokosawa, 2021
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

EPSTOPDF := $(shell which epstopdf 2>/dev/null)
GS_953_OR_LATER := $(shell gs --version | grep -c -E "9\.5[3-9].?")
GS_OPT=--gsopt=-dPDFSETTINGS=/ebook

$(PDFTARGETS_OF_GNUPLOT_NEEDFIXFONTS): $(FIXFONTS)
$(PDFTARGETS_OF_GNUPLOT_NEEDFIXFONTS): %.pdf: %.eps
	@echo "$< --> $(suffix $@)"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
	@sh $(FIXFONTS) < $< > $(basename $<)__.eps
	@eps2eps $(basename $<)__.eps $(basename $<)___.eps
	@epstopdf $(GS_OPT) $(basename $<)___.eps $@
	@rm -f $(basename $<)__.eps $(basename $<)___.eps

$(PDFTARGETS_OF_TEX): %.pdf: %.eps
	@echo "$< --> $(suffix $@)"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
ifeq ($(GS_953_OR_LATER),1)
	@eps2eps -dALLOWPSTRANSPARENCY $< $(basename $<)__.eps
	@epstopdf --gsopt=-dALLOWPSTRANSPARENCY $(GS_OPT) $(basename $<)__.eps $@
else
	@eps2eps -dNOSAFER $< $(basename $<)__.eps
	@epstopdf --nosafer $(GS_OPT) $(basename $<)__.eps $@
endif
	@rm -f $(basename $<)__.eps

$(PDFTARGETS_OF_EPSORIG_NOFIXFONTS) $(PDFTARGETS_OF_EPSOTHER): %.pdf: %.eps
	@echo "$< --> $(suffix $@)"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
	@eps2eps $< $(basename $<)__.eps
	@epstopdf $(GS_OPT) $(basename $<)__.eps $@
	@rm -f $(basename $<)__.eps
