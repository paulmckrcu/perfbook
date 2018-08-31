LATEXSOURCES = \
	perfbook.tex \
	legal.tex \
	glossary.tex \
	qqz.sty origpub.sty \
	noindentafter.sty \
	pfbook.cls \
	ushyphex.tex pfhyphex.tex \
	*/*.tex \
	*/*/*.tex

LATEXGENERATED = autodate.tex qqz.tex contrib.tex origpub.tex

ABBREVTARGETS := tcb 1c hb msns mss mstx msr msn msnt 1csf

PDFTARGETS := perfbook.pdf $(foreach v,$(ABBREVTARGETS),perfbook-$(v).pdf)

EPSSOURCES_FROM_TEX := \
	SMPdesign/DiningPhilosopher5.eps \
	SMPdesign/DiningPhilosopher5TB.eps \
	SMPdesign/DiningPhilosopher4part-b.eps \
	SMPdesign/DiningPhilosopher5PEM.eps

DOTSOURCES := $(wildcard */*.dot)

EPSSOURCES_FROM_DOT := $(DOTSOURCES:%.dot=%.eps)

FIGSOURCES := $(wildcard */*.fig) $(wildcard */*/*.fig)

EPSSOURCES_FROM_FIG := $(FIGSOURCES:%.fig=%.eps)

EPSSOURCES_DUP := \
	$(wildcard */*.eps) \
	$(wildcard */*/*.eps) \
	$(EPSSOURCES_FROM_TEX) \
	$(EPSSOURCES_FROM_DOT) \
	$(EPSSOURCES_FROM_FIG)

EPSSOURCES := $(sort $(EPSSOURCES_DUP))

PDFTARGETS_OF_EPS := $(EPSSOURCES:%.eps=%.pdf)

EPSORIGIN := $(filter-out $(EPSSOURCES_FROM_TEX) $(EPSSOURCES_FROM_DOT) $(EPSSOURCES_FROM_FIG),$(EPSSOURCES))

PDFTARGETS_OF_EPSORIG := $(EPSORIGIN:%.eps=%.pdf)

PDFTARGETS_OF_EPSOTHER := $(filter-out $(PDFTARGETS_OF_EPSORIG),$(PDFTARGETS_OF_EPS))

BIBSOURCES := bib/*.bib alphapf.bst

SVGSOURCES := $(wildcard */*.svg)
SVG_LARGE_BITMAP := future/ibmqx2-labeled.svg
PDFTARGETS_OF_SVG := $(filter-out $(SVG_LARGE_BITMAP:%.svg=%.pdf),$(SVGSOURCES:%.svg=%.pdf))
PNGTARGETS_OF_SVG := $(SVG_LARGE_BITMAP:%.svg=%.png)
TARGETS_OF_SVG :=  $(PDFTARGETS_OF_SVG) $(PNGTARGETS_OF_SVG)

DOT := $(shell which dot 2>/dev/null)
FIG2EPS := $(shell which fig2eps 2>/dev/null)
A2PING := $(shell which a2ping 2>/dev/null)
INKSCAPE := $(shell which inkscape 2>/dev/null)
LATEXPAND := $(shell which latexpand 2>/dev/null)
STEELFONT := $(shell fc-list | grep -c -i steel)
URWPS := $(shell fc-list | grep "Nimbus Mono PS" | wc -l)

ifeq ($(URWPS),0)
FIXSVGFONTS   = utilities/fixsvgfonts.sh
FIXANEPSFONTS = utilities/fixanepsfonts.sh
else
FIXSVGFONTS   = utilities/fixsvgfonts-urwps.sh
FIXANEPSFONTS = utilities/fixanepsfonts-urwps.sh
endif

STEELFONTID := $(shell fc-list | grep -i steel | grep -c Steel)

ifdef A2PING
A2PING_277P := $(shell a2ping --help 2>&1 | grep -c "2.77p,")
ifeq ($(A2PING_277P),1)
GS_VER := $(shell gs --version)
A2PING_GSCNFL := $(shell env printf "%05.2f\n%05.2f\n" $(GS_VER) 9.22 | \
	sort | head -1 | grep -c "09.22")
else
A2PING_GSCNFL := 0
endif
endif

SOURCES_OF_SNIPPET := $(shell grep -r -l -F '\begin{snippet}' CodeSamples)
GEN_SNIPPET_D  = utilities/gen_snippet_d.pl utilities/gen_snippet_d.sh

default = $(PERFBOOK_DEFAULT)

ifeq ($(default),)
	targ = perfbook.pdf
else
	targ = $(default)
endif

.PHONY: all touchsvg clean distclean neatfreak 2c ls-unused $(ABBREVTARGETS) mslm perfbook-mslm.pdf mslmmsg help
all: $(targ)

ifeq ($(MAKECMDGOALS),clean)
else ifeq ($(MAKECMDGOALS),distclean)
else ifeq ($(MAKECMDGOALS),neatfreak)
else
-include CodeSamples/snippets.d
endif

2c: perfbook.pdf

mslm: perfbook-mslm.pdf

perfbook-mslm.pdf: perfbook.pdf mslmmsg

mslmmsg:
	@echo "perfbook-mslm.pdf is promoted to default target,"
	@echo "built as perfbook.pdf."

$(PDFTARGETS): %.pdf: %.tex %.bbl
	sh utilities/runlatex.sh $(basename $@)

$(PDFTARGETS:.pdf=.bbl): %.bbl: %.aux $(BIBSOURCES)
	bibtex $(basename $@)

$(PDFTARGETS:.pdf=.aux): $(LATEXGENERATED) $(LATEXSOURCES)
	sh utilities/runfirstlatex.sh $(basename $@)

autodate.tex: perfbook.tex $(LATEXSOURCES) $(BIBSOURCES) $(SVGSOURCES) $(FIGSOURCES) $(DOTSOURCES) $(EPSORIGIN) $(SOURCES_OF_SNIPPET) utilities/fcvextract.pl
	sh utilities/autodate.sh >autodate.tex

perfbook_flat.tex: autodate.tex $(PDFTARGETS_OF_EPS) $(TARGETS_OF_SVG) $(FCVSNIPPETS)
ifndef LATEXPAND
	$(error --> $@: latexpand not found. Please install it)
endif
	echo > qqz.tex
	echo > contrib.tex
	echo > origpub.tex
	latexpand --empty-comments perfbook.tex 1> $@ 2> /dev/null

qqz.tex: perfbook_flat.tex
	sh utilities/extractqqz.sh < $< | perl utilities/qqzreorder.pl > $@

contrib.tex: perfbook_flat.tex qqz.tex
	cat $^ | sh utilities/extractcontrib.sh > $@

origpub.tex: perfbook_flat.tex
	sh utilities/extractorigpub.sh < $< > $@

perfbook-tcb.tex: perfbook.tex
	sed -e 's/{tblcptop}{true}/{tblcptop}{false}/' < $< > $@

perfbook-1c.tex: perfbook.tex
	sed -e 's/,twocolumn//' -e 's/setboolean{twocolumn}{true}/setboolean{twocolumn}{false}/' < $< > $@

perfbook-hb.tex: perfbook.tex
	sed -e 's/,twocolumn/&,letterpaperhb/' -e 's/setboolean{hardcover}{false}/setboolean{hardcover}{true}/' < $< > $@

perfbook-msns.tex: perfbook.tex
	sed -e 's/%msfontstub/\\usepackage{courier}/' \
	    -e 's/{lmttforcode}{true}/{lmttforcode}{false}/' < $< > $@

perfbook-mss.tex: perfbook.tex
	sed -e 's/%msfontstub/\\usepackage[scaled=.94]{couriers}/' \
	    -e 's/{lmttforcode}{true}/{lmttforcode}{false}/' < $< > $@

perfbook-mstx.tex: perfbook.tex
	sed -e 's/%msfontstub/\\renewcommand*\\ttdefault{txtt}/' < $< > $@

perfbook-msr.tex: perfbook.tex
	sed -e 's/%msfontstub/\\usepackage[scaled=.94]{nimbusmono}/' < $< > $@
	@echo "## This target requires font package nimbus15. ##"

perfbook-msn.tex: perfbook.tex
	sed -e 's/%msfontstub/\\usepackage{nimbusmononarrow}/' < $< > $@
	@echo "## This target requires font package nimbus15. ##"

perfbook-msnt.tex: perfbook.tex
	sed -e 's/%msfontstub/\\usepackage[zerostyle=a]{newtxtt}/' < $< > $@
	@echo "## This target requires font package newtxtt. ##"
	@echo "## If build fails, try target 'mstx' instead. ##"

perfbook-1csf.tex: perfbook-1c.tex
	sed -e 's/setboolean{sansserif}{false}/setboolean{sansserif}{true}/' \
	    -e 's/%msfontstub/\\usepackage[var0]{inconsolata}[2013\/07\/17]/' < $< > $@
	@echo "## This target requires math font package newtxsf. ##"

# Rules related to perfbook_html are removed as of May, 2016

$(EPSSOURCES_FROM_TEX): %.eps: %.tex
	@echo "$< --> $@"
	sh utilities/mpostcheck.sh
	@latex -output-directory=$(shell dirname $<) $< > /dev/null 2>&1
	@dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@ > /dev/null 2>&1
	@sh $(FIXANEPSFONTS) $@

$(EPSSOURCES_FROM_DOT): %.eps: %.dot
	@echo "$< --> $@"
ifndef DOT
	$(error $< --> $@: dot not found. Please install graphviz)
endif
	@dot -Tps -o $@ $<
	@sh $(FIXANEPSFONTS) $@

$(EPSSOURCES_FROM_FIG): %.eps: %.fig
	@echo "$< --> $@"
ifndef FIG2EPS
	$(error $< --> $@: fig2eps not found. Please install fig2ps)
endif
	@fig2eps --nogv $< > /dev/null 2>&1
	@sh $(FIXANEPSFONTS) $@

$(PDFTARGETS_OF_EPSORIG): %.pdf: %.eps
	@echo "$< --> $@"
ifndef A2PING
	$(error $< --> $@: a2ping not found. Please install it)
endif
ifeq ($(A2PING_GSCNFL),1)
	$(error a2ping version conflict. See #7 in FAQ-BUILD.txt)
endif
	@cp $< $<i
	@sh $(FIXANEPSFONTS) $<i
	@a2ping --below --hires --bboxfrom=compute-gs $<i $@ > /dev/null 2>&1
	@rm -f $<i

$(PDFTARGETS_OF_EPSOTHER): %.pdf: %.eps
	@echo "$< --> $@"
ifndef A2PING
	$(error $< --> $@: a2ping not found. Please install it)
endif
ifeq ($(A2PING_GSCNFL),1)
	$(error a2ping version conflict. See #7 in FAQ-BUILD.txt)
endif
	@a2ping --below --hires --bboxfrom=compute-gs $< $@ > /dev/null 2>&1

$(PDFTARGETS_OF_SVG): %.pdf: %.svg
	@echo "$< --> $@"
ifeq ($(STEELFONT),0)
	$(error "Steel City Comic" font not found. See #1 in FAQ.txt)
endif
ifndef INKSCAPE
	$(error $< --> $@ inkscape not found. Please install it)
endif
ifeq ($(STEELFONTID),0)
	@sh $(FIXSVGFONTS) < $< | sed -e 's/Steel City Comic/Test/g' > $<i
else
	@sh $(FIXSVGFONTS) < $< > $<i
endif
	@inkscape --export-pdf=$@ $<i > /dev/null 2>&1
	@rm -f $<i

$(PNGTARGETS_OF_SVG): %.png: %.svg
	@echo "$< --> $@"
ifndef INKSCAPE
	$(error $< --> $@: inkscape not found. Please install it)
endif
ifeq ($(STEELFONTID),0)
	@sh $(FIXSVGFONTS) < $< | sed -e 's/Steel City Comic/Test/g' > $<i
else
	@sh $(FIXSVGFONTS) < $< > $<i
endif
	@inkscape --export-dpi=200 --export-png=$@ $<i > /dev/null 2>&1
	@rm -f $<i

CodeSamples/snippets.d: $(SOURCES_OF_SNIPPET) $(GEN_SNIPPET_D)
	sh ./utilities/gen_snippet_d.sh

$(FCVSNIPPETS):
	@echo "$< --> $@"
	@utilities/fcvextract.pl $< $(subst @,:,$(basename $(notdir $@))) > $@

help:
	@echo "Official targets (Latin Modern Typewriter for monospace font):"
	@echo "  Full,              Abbr."
	@echo "  perfbook.pdf,      2c:   (default) 2-column layout"
	@echo "  perfbook-1c.pdf,   1c:   1-column layout"
	@echo "  perfbook-hb.pdf,   hb:   For hardcover books (2-column)"
	@echo
	@echo "Experimental targets:"
	@echo "  Full,              Abbr."
	@echo "  perfbook-tcb,      tcb:  2c with table caption at bottom (prev default)"
	@echo "  perfbook-msnt.pdf, msnt: 2c with newtxtt as monospace (non-slashed 0)"
	@echo "  perfbook-mstx.pdf, mstx: 2c with txtt as monospace"
	@echo "  perfbook-msr.pdf,  msr:  2c with regular thickness courier clone"
	@echo "  perfbook-msn.pdf,  msn:  2c with narrow courier clone"

	@echo "  perfbook-1csf.pdf, 1csf: 1c with sans serif font"
	@echo "  perfbook-msns.pdf, msns: 2c with non-scaled courier (orig default)"
	@echo "  perfbook-mss.pdf,  mss:  2c with scaled courier (prev default)"
	@echo "  \"msnt\" requires \"newtxtt\". \"mstx\" is fallback target for older TeX env."
	@echo "  \"msr\" and \"msn\" require \"nimbus15\"."
	@echo "  \"msn\" doesn't cover bold face for monospace."
	@echo "  \"1csf\" requires \"newtxsf\"."
	@echo
	@echo "All targets except for \"msns\" and \"mss\" use \"Latin Modern Typewriter\" font"
	@echo "for code snippets."

clean:
	find . -name '*.aux' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' \
		-o -name '*.qqz' -o -name '*.toc' -o -name '*.bbl' \
		-o -name '*.fcv' | xargs rm -f
	rm -f perfbook_flat.tex perfbook*.out perfbook-*.tex
	rm -f $(LATEXGENERATED)
	rm -f $(SVG_LARGE_BITMAP:%.svg=%.pdf) $(PNGTARGETS_OF_SVG)
	rm -f extraction
	rm -f CodeSamples/snippets.mk CodeSamples/snippets.d

distclean: clean
	sh utilities/cleanpdf.sh
	rm -f $(EPSSOURCES_FROM_DOT) $(EPSSOURCES_FROM_TEX) $(EPSSOURCES_FROM_FIG)

touchsvg:
	find . -name '*.svg' | xargs touch

ls-unused:
	find . -name .unused | xargs ls

neatfreak: distclean
	find . -name '*.pdf' | xargs rm -f

.SECONDEXPANSION:
$(ABBREVTARGETS): %: perfbook-$$@.pdf
