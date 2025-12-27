# SPDX-License-Identifier: GPL-2.0-or-later
#
# Copyright (C) Akira Yokosawa, 2021
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

EPSTOPDF := $(shell $(WHICH) epstopdf 2>/dev/null)
GS_953_OR_LATER := $(shell gs --version | grep -c -E "^(9\.5[3-9]|10\.[0-9]).?")
GS_OPT=--gsopt=-dPDFSETTINGS=/ebook

$(PDFTARGETS_OF_GNUPLOT_NEEDFIXFONTS): $(FIXFONTS)
$(PDFTARGETS_OF_GNUPLOT_NEEDFIXFONTS): %.pdf: %.eps
	@echo "$< --> $(suffix $@)"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
	@TMP=`mktemp -d` && \
	    TMP1=$$TMP/$(notdir $(basename $<)__.eps) && \
	    TMP2=$$TMP/$(notdir $(basename $<)___.eps) && \
	    TMPDST=$$TMP/$(notdir $@) && \
	    sh $(FIXFONTS) < $< > $$TMP1 && \
	    eps2eps $$TMP1 $$TMP2 && \
	    epstopdf $(GS_OPT) $$TMP2 $$TMPDST && \
	    mv -f $$TMPDST $@ && \
	    rm -rf $$TMP

$(PDFTARGETS_OF_TEX): %.pdf: %.eps
	@echo "$< --> $(suffix $@)"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
ifeq ($(GS_953_OR_LATER),1)
	@TMP=`mktemp -d` && \
	    TMPSRC=$$TMP/$(notdir $<) && \
	    TMP1=$$TMP/$(notdir $(basename $<)__.eps) && \
	    TMPDST=$$TMP/$(notdir $@) && \
	    cp $< $$TMPSRC && \
	    eps2eps -dALLOWPSTRANSPARENCY $$TMPSRC $$TMP1 && \
	    epstopdf --gsopt=-dALLOWPSTRANSPARENCY $(GS_OPT) $$TMP1 $$TMPDST && \
	    mv -f $$TMPDST $@ && \
	    rm -rf $$TMP
else
	@TMP=`mktemp -d` && \
	    TMPSRC=$$TMP/$(notdir $<) && \
	    TMP1=$$TMP/$(notdir $(basename $<)__.eps) && \
	    TMPDST=$$TMP/$(notdir $@) && \
	    cp $< $$TMPSRC && \
	    eps2eps -dNOSAFER $$TMPSRC $$TMP1 && \
	    epstopdf --nosafer $(GS_OPT) $$TMP1 $$TMPDST && \
	    mv -f $$TMPDST $@ && \
	    rm -rf $$TMP
endif

$(PDFTARGETS_OF_EPSORIG_NOFIXFONTS) $(PDFTARGETS_OF_EPSOTHER): %.pdf: %.eps
	@echo "$< --> $(suffix $@)"
ifndef EPSTOPDF
	$(error $< --> $@: epstopdf not found. Please install it)
endif
	@TMP=`mktemp -d` && \
	    TMPSRC=$$TMP/$(notdir $<) && \
	    TMP1=$$TMP/$(notdir $(basename $<)__.eps) && \
	    TMPDST=$$TMP/$(notdir $@) && \
	    cp $< $$TMPSRC && \
	    eps2eps $$TMPSRC $$TMP1 && \
	    epstopdf $(GS_OPT) $$TMP1 $$TMPDST && \
	    mv -f $$TMPDST $@ && \
	    rm -rf $$TMP
