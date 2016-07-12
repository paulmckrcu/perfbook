LATEXSOURCES = \
	perfbook.tex \
	legal.tex \
	qqz.sty origpub.sty \
	*/*.tex \
	*/*/*.tex

EPSSOURCES_FROM_TEX := \
	SMPdesign/DiningPhilosopher5.eps \
	SMPdesign/DiningPhilosopher5TB.eps \
	SMPdesign/DiningPhilosopher4part-b.eps \
	SMPdesign/DiningPhilosopher5PEM.eps

DOTSOURCES := $(wildcard */*.dot)

EPSSOURCES_FROM_DOT := $(DOTSOURCES:%.dot=%.eps)

EPSSOURCES_DUP := \
	$(wildcard */*.eps) \
	$(wildcard */*/*.eps) \
	$(EPSSOURCES_FROM_TEX) \
	$(EPSSOURCES_FROM_DOT)

EPSSOURCES := $(sort $(EPSSOURCES_DUP))

PDFTARGETS_OF_EPS := $(EPSSOURCES:%.eps=%.pdf)

BIBSOURCES = bib/*.bib

SVGSOURCES := $(wildcard */*.svg)

PDFTARGETS_OF_SVG := $(SVGSOURCES:%.svg=%.pdf)

default = $(PERFBOOK_DEFAULT)

ifeq ($(default),)
	targ = perfbook.pdf
else
	targ = $(default)
endif

.PHONY: all touchsvg clean distclean neatfreak 1c 2c hb ls-unused
all: $(targ)

1c: perfbook-1c.pdf

2c: perfbook.pdf

hb: perfbook-hb.pdf

perfbook.pdf: perfbook.bbl
	sh utilities/runlatex.sh perfbook

perfbook.bbl: $(BIBSOURCES) perfbook.aux
	bibtex perfbook

perfbook.aux: $(LATEXSOURCES) extraction
	sh utilities/runfirstlatex.sh perfbook

perfbook_flat.tex qqz.tex: perfbook.tex $(LATEXSOURCES) $(EPSSOURCES) $(PDFTARGETS_OF_EPS) $(PDFTARGETS_OF_SVG)
	echo > qqz.tex
	texexpand perfbook.tex > perfbook_flat.tex
	sh utilities/extractqqz.sh < perfbook_flat.tex > qqz.tex

extraction: perfbook_flat.tex
	cat perfbook_flat.tex qqz.tex | sh utilities/extractcontrib.sh > contrib.tex
	sh utilities/extractorigpub.sh < perfbook_flat.tex > origpub.tex
	touch extraction

perfbook-1c.pdf: perfbook-1c.tex perfbook-1c.bbl
	sh utilities/runlatex.sh perfbook-1c

perfbook-1c.tex: perfbook.tex
	sed -e 's/,twocolumn//' -e '/^\\frontmatter/a \\\\pagestyle{plain}' -e 's/setboolean{twocolumn}{true}/setboolean{twocolumn}{false}/' < perfbook.tex > perfbook-1c.tex

perfbook-1c.bbl: $(BIBSOURCES) perfbook-1c.aux
	bibtex perfbook-1c

perfbook-1c.aux: $(LATEXSOURCES) extraction
	sh utilities/runfirstlatex.sh perfbook-1c

perfbook-hb.pdf: perfbook-hb.tex perfbook-hb.bbl
	sh utilities/runlatex.sh perfbook-hb

perfbook-hb.tex: perfbook.tex
	sed -e 's/,twocolumn/&,letterpaperhb/' -e 's/setboolean{hardcover}{false}/setboolean{hardcover}{true}/' < perfbook.tex > perfbook-hb.tex

perfbook-hb.bbl: $(BIBSOURCES) perfbook-hb.aux
	bibtex perfbook-hb

perfbook-hb.aux: $(LATEXSOURCES) extraction
	sh utilities/runfirstlatex.sh perfbook-hb

# Rules related to perfbook_html are removed as of May, 2016

$(EPSSOURCES_FROM_TEX): %.eps: %.tex
	@echo "$< --> $@"
	@latex -output-directory=$(shell dirname $<) $<
	@dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@
	@sh utilities/fixanepsfonts.sh $@

$(EPSSOURCES_FROM_DOT): %.eps: %.dot
	@echo "$< --> $@"
	@dot -Tps -o $@ $<
	@sh utilities/fixanepsfonts.sh $@

$(PDFTARGETS_OF_EPS): %.pdf: %.eps
	@echo "$< --> $@"
	@a2ping --below --hires --bboxfrom=compute-gs $< $@ > /dev/null 2>&1

$(PDFTARGETS_OF_SVG): %.pdf: %.svg
	@echo "$< --> $@"
	@inkscape --export-pdf=$@ $<

clean:
	find . -name '*.aux' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' \
		-o -name '*.qqz' -o -name '*.toc' -o -name '*.bbl' | xargs rm -f
	rm -f perfbook_flat.tex perfbook.out perfbook-1c.out
	rm -f qqz.tex
	rm -f perfbook-hb.out perfbook-1c.tex perfbook-hb.tex
	rm -f extraction

distclean: clean
	sh utilities/cleanpdf.sh
	rm -f $(EPSSOURCES_FROM_DOT) $(EPSSOURCES_FROM_TEX)

touchsvg:
	find . -name '*.svg' | xargs touch

ls-unused:
	find . -name .unused | xargs ls

neatfreak: distclean
	# Don't forget to regenerate the .pdf from each .svg file
	find . -name '*.pdf' | xargs rm -f

# Note on why 'extraction' should be an empty target
#
# There are dependency loops around perfbook_flat.tex.
# perfbook_flat.tex requires an empty qqz.tex and up-to-date
# contrib.tex and origpub.tex for texexpand to work properly.
#
# Both contrib.tex and origpub.tex requires perfbook_flat.tex.
# contrib.tex also requires up-to-date qqz.tex.
#
# So at first glance, rules for contrib.tex and origpub.tex
# can be defined, but that requires 'extraction' to be a phony
# target.
#
# 'extraction' is prerequisite for perfbook.aux.
# If you make it a phony target, the rule for perfbook.aux is
# always executed. That means runfirstlatex.run will run even
# if no source file is updated.
# To avoid the redundant run, we need to make 'extraction' an
# empty target.
