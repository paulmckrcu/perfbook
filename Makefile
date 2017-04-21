LATEXSOURCES = \
	perfbook.tex \
	legal.tex \
	glossary.tex \
	qqz.sty origpub.sty \
	book.cls \
	ushyphex.tex pfhyphex.tex \
	*/*.tex \
	*/*/*.tex

LATEXGENERATED = autodate.tex qqz.tex contrib.tex origpub.tex

ABBREVTARGETS := 1c hb msns mss mstx msr msn msnt 1csf

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

BIBSOURCES := bib/*.bib alphapf.bst

SVGSOURCES := $(wildcard */*.svg)

PDFTARGETS_OF_SVG := $(SVGSOURCES:%.svg=%.pdf)

DOT := $(shell which dot 2>/dev/null)

FIG2EPS := $(shell which fig2eps 2>/dev/null)

A2PING := $(shell which a2ping 2>/dev/null)

INKSCAPE := $(shell which inkscape 2>/dev/null)

default = $(PERFBOOK_DEFAULT)

ifeq ($(default),)
	targ = perfbook.pdf
else
	targ = $(default)
endif

.PHONY: all touchsvg clean distclean neatfreak 2c ls-unused $(ABBREVTARGETS) mslm perfbook-mslm.pdf mslmmsg help
all: $(targ)

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

autodate.tex: $(LATEXSOURCES) $(BIBSOURCES) $(SVGSOURCES) $(FIGSOURCES) $(DOTSOURCES)
	sh utilities/autodate.sh >autodate.tex

perfbook_flat.tex: perfbook.tex $(LATEXSOURCES) $(PDFTARGETS_OF_EPS) $(PDFTARGETS_OF_SVG)
	echo > qqz.tex
	echo > contrib.tex
	echo > origpub.tex
	texexpand perfbook.tex > $@

qqz.tex: perfbook_flat.tex
	sh utilities/extractqqz.sh < $< | perl utilities/qqzreorder.pl > $@

contrib.tex: perfbook_flat.tex qqz.tex
	cat $^ | sh utilities/extractcontrib.sh > $@

origpub.tex: perfbook_flat.tex
	sh utilities/extractorigpub.sh < $< > $@

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
	@echo "## This target requires recent version (>= 1.3i) of mathastext. ##"

# Rules related to perfbook_html are removed as of May, 2016

$(EPSSOURCES_FROM_TEX): %.eps: %.tex
	@echo "$< --> $@"
	sh utilities/mpostcheck.sh
	@latex -output-directory=$(shell dirname $<) $< > /dev/null 2>&1
	@dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@ > /dev/null 2>&1
	@sh utilities/fixanepsfonts.sh $@

$(EPSSOURCES_FROM_DOT): %.eps: %.dot
	@echo "$< --> $@"
ifndef DOT
	$(error "$< --> $@: dot not found. Please install graphviz")
endif
	@dot -Tps -o $@ $<
	@sh utilities/fixanepsfonts.sh $@

$(EPSSOURCES_FROM_FIG): %.eps: %.fig
	@echo "$< --> $@"
ifndef FIG2EPS
	$(error "$< --> $@: fig2eps not found. Please install fig2ps")
endif
	@fig2eps --nogv $< > /dev/null 2>&1
	@sh utilities/fixanepsfonts.sh $@

$(PDFTARGETS_OF_EPS): %.pdf: %.eps
	@echo "$< --> $@"
ifndef A2PING
	$(error "$< --> $@: a2ping not found. Please install it.")
endif
	@a2ping --below --hires --bboxfrom=compute-gs $< $@ > /dev/null 2>&1

$(PDFTARGETS_OF_SVG): %.pdf: %.svg
	@echo "$< --> $@"
ifndef INKSCAPE
	$(error "$< --> $@: inkscape not found. Please install it.")
endif
	@inkscape --export-pdf=$@ $<

help:
	@echo "Official targets (Latin Modern Typewriter for monospace font):"
	@echo "  Full,              Abbr."
	@echo "  perfbook.pdf,      2c:   (default) 2-column layout"
	@echo "  perfbook-1c.pdf,   1c:   1-column layout"
	@echo "  perfbook-hb.pdf,   hb:   For hardcover books (2-column)"
	@echo
	@echo "Experimental targets:"
	@echo "  Full,              Abbr."
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
	@echo "  \"1csf\" requires recent version (>=1.3i) of \"mathastext\"."
	@echo
	@echo "All targets except for \"msns\" and \"mss\" use \"Latin Modern Typewriter font"
	@echo "for code snippets."

clean:
	find . -name '*.aux' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' \
		-o -name '*.qqz' -o -name '*.toc' -o -name '*.bbl' | xargs rm -f
	rm -f perfbook_flat.tex perfbook*.out perfbook-*.tex
	rm -f $(LATEXGENERATED)
	rm -f extraction

distclean: clean
	sh utilities/cleanpdf.sh
	rm -f $(EPSSOURCES_FROM_DOT) $(EPSSOURCES_FROM_TEX) $(EPSSOURCES_FROM_FIG)

touchsvg:
	find . -name '*.svg' | xargs touch

ls-unused:
	find . -name .unused | xargs ls

neatfreak: distclean
	# Don't forget to regenerate the .pdf from each .svg file
	find . -name '*.pdf' | xargs rm -f

.SECONDEXPANSION:
$(ABBREVTARGETS): %: perfbook-$$@.pdf
