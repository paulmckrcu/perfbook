# SPDX-License-Identifier: GPL-2.0-or-later
#
# Copyright (C) Akira Yokosawa, 2021
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

EPSTOPDF := $(shell which epstopdf 2>/dev/null)
GS_953_OR_LATER := $(shell gs --version | grep -c -E "9\.5[3-9].?")

$(PDFTARGETS_OF_EPSORIG): %.pdf: %.eps
	@echo "$< --> $@"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
	@cp $< $(basename $<)__.eps
	@sh $(FIXANEPSFONTS) $(basename $<)__.eps
	@eps2eps $(basename $<)__.eps $(basename $<)___.eps
	@epstopdf $(basename $<)___.eps $@
	@rm -f $(basename $<)__.eps $(basename $<)___.eps

$(PDFTARGETS_OF_TEX): %.pdf: %.eps
	@echo "$< --> $@"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
ifeq ($(GS_953_OR_LATER),1)
	@eps2eps -dALLOWPSTRANSPARENCY $< $(basename $<)__.eps
	@epstopdf --gsopt=-dALLOWPSTRANSPARENCY $(basename $<)__.eps $@
else
	@eps2eps $< $(basename $<)__.eps
	@epstopdf --nosafer $(basename $<)__.eps $@
endif
	@rm -f $(basename $<)__.eps

$(PDFTARGETS_OF_EPSOTHER): %.pdf: %.eps
	@echo "$< --> $@"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
	@eps2eps $< $(basename $<)__.eps
	@epstopdf $(basename $<)__.eps $@
	@rm -f $(basename $<)__.eps
