LATEXSOURCES = \
	perfbook.tex \
	legal.tex \
	qqz.sty origpub.sty \
	advsync/*.tex \
	appendix/*.tex \
	appendix/ack/*.tex \
	appendix/primitives/*.tex \
	appendix/questions/*.tex \
	appendix/whymb/*.tex \
	count/*.tex \
	cpu/*.tex \
	datastruct/*.tex \
	debugging/*.tex \
	easy/*.tex \
	glossary.tex \
	intro/*.tex \
	memalloc/*.tex \
	owned/*.tex \
	defer/*.tex \
	formal/*.tex \
	future/*.tex \
	howto/*.tex \
	SMPdesign/*.tex \
	locking/*.tex \
	together/*.tex \
	toolsoftrade/*.tex

EPSTARGETS_OF_TEX = \
	SMPdesign/DiningPhilosopher5.eps \
	SMPdesign/DiningPhilosopher5TB.eps \
	SMPdesign/DiningPhilosopher4part-b.eps \
	SMPdesign/DiningPhilosopher5PEM.eps

EPSTARGETS_OF_DOT = \
	advsync/store15tred.eps \
	count/sig-theft.eps

EPSSOURCES = \
	SMPdesign/*.eps \
	advsync/*.eps \
	appendix/questions/*.eps \
	appendix/whymb/*.eps \
	count/*.eps \
	cpu/*.eps \
	datastruct/*.eps \
	defer/*.eps \
	easy/*.eps \
	future/*.eps \
	intro/*.eps \
	locking/*.eps \
	$(EPSTARGETS_OF_TEX)

BIBSOURCES = bib/*.bib

SVGSOURCES = \
	cartoons/*.svg \
	debugging/*.svg \
	count/*.svg \
	SMPdesign/*.svg \
	defer/*.svg \
	datastruct/*.svg \
	rt/*.svg

default = $(PERFBOOK_DEFAULT)

ifeq ($(default),)
	targ = perfbook.pdf
else
	targ = $(default)
endif

.PHONY: all touchsvg clean distclean neatfreak 1c 2c hb
all: $(targ)

1c: perfbook-1c.pdf

2c: perfbook.pdf

hb: perfbook-hb.pdf

perfbook.pdf: perfbook.bbl
	sh utilities/runlatex.sh perfbook

perfbook.bbl: $(BIBSOURCES) perfbook.aux
	bibtex perfbook

perfbook.aux: $(LATEXSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook

perfbook_flat.tex qqz.tex: perfbook.tex $(LATEXSOURCES) $(EPSSOURCES) embedfonts
	echo > qqz.tex
	texexpand perfbook.tex > perfbook_flat.tex
	sh utilities/extractqqz.sh < perfbook_flat.tex > qqz.tex

extraction: perfbook_flat.tex
	cat perfbook_flat.tex qqz.tex | sh utilities/extractcontrib.sh > contrib.tex
	sh utilities/extractorigpub.sh < perfbook_flat.tex > origpub.tex
	touch extraction

embedfonts: $(EPSSOURCES) $(SVGSOURCES)
	sh utilities/fixfigfonts.sh
	sh utilities/fixdotfonts.sh
	sh utilities/eps2pdf.sh
	touch embedfonts

perfbook-1c.pdf: perfbook-1c.tex perfbook-1c.bbl
	sh utilities/runlatex.sh perfbook-1c

perfbook-1c.tex: perfbook.tex
	sed -e 's/,twocolumn//' -e '/^\\frontmatter/a \\\\pagestyle{plain}' -e 's/setboolean{twocolumn}{true}/setboolean{twocolumn}{false}/' < perfbook.tex > perfbook-1c.tex

perfbook-1c.bbl: $(BIBSOURCES) perfbook-1c.aux
	bibtex perfbook-1c

perfbook-1c.aux: $(LATEXSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook-1c

perfbook-hb.pdf: perfbook-hb.tex perfbook-hb.bbl
	sh utilities/runlatex.sh perfbook-hb

perfbook-hb.tex: perfbook.tex
	sed -e 's/,twocolumn/&,letterpaperhb/' -e 's/setboolean{hardcover}{false}/setboolean{hardcover}{true}/' < perfbook.tex > perfbook-hb.tex

perfbook-hb.bbl: $(BIBSOURCES) perfbook-hb.aux
	bibtex perfbook-hb

perfbook-hb.aux: $(LATEXSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook-hb

# Rules related to perfbook_html are removed as of May, 2016

$(EPSTARGETS_OF_TEX): %.eps: %.tex
	latex -output-directory=$(shell dirname $<) $<
	dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@
	sh utilities/fixanepsfonts.sh $@

$(EPSTARGETS_OF_DOT): %.eps: %.dot
	dot -Tps -o $@ $<

clean:
	find . -name '*.aux' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' \
		-o -name '*.qqz' -o -name '*.toc' -o -name '*.bbl' | xargs rm -f
	rm -f perfbook_flat.tex perfbook.out perfbook-1c.out
	rm -f qqz.tex
	rm -f perfbook-hb.out perfbook-1c.tex perfbook-hb.tex
	rm -f extraction embedfonts

distclean: clean
	sh utilities/cleanpdf.sh

touchsvg:
	find . -name '*.svg' | xargs touch

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
