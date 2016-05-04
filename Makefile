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

PDFTARGETS_OF_DOT = \
	advsync/store15tred.pdf

EPSTARGETS_OF_DOT = \
	count/sig-theft.eps

EPS_NOT_IN_REPO = \
	$(EPSTARGETS_OF_TEX) \
	$(EPSTARGETS_OF_DOT)

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
	$(PDFTARGETS_OF_DOT) \
	$(EPS_NOT_IN_REPO)

BIBSOURCES = \
	bib/*.bib

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

2c: perfbook.pdf

1c: perfbook-1c.pdf

hb: perfbook-hb.pdf

perfbook.pdf: perfbook.bbl
	sh utilities/runlatex.sh perfbook

perfbook.bbl: $(BIBSOURCES) perfbook_aux
	bibtex perfbook

perfbook_aux: $(LATEXSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook
	touch perfbook_aux

perfbook_flat.tex: perfbook.tex $(LATEXSOURCES) $(EPSSOURCES) embedfonts
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

perfbook-1c.bbl: $(BIBSOURCES) perfbook-1c_aux
	bibtex perfbook-1c

perfbook-1c_aux: $(LATEXSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook-1c
	touch perfbook-1c_aux

perfbook-hb.pdf: perfbook-hb.tex perfbook-hb.bbl
	sh utilities/runlatex.sh perfbook-hb

perfbook-hb.tex: perfbook.tex
	sed -e 's/,twocolumn/&,letterpaperhb/' -e 's/setboolean{hardcover}{false}/setboolean{hardcover}{true}/' < perfbook.tex > perfbook-hb.tex

perfbook-hb.bbl: $(BIBSOURCES) perfbook-hb_aux
	bibtex perfbook-hb

perfbook-hb_aux: $(LATEXSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook-hb
	touch perfbook-hb_aux

qqz_html.tex: qqz.tex
	sh utilities/prep4html.sh < qqz.tex > qqz_html.tex

origpub_html.tex: origpub.tex
	sh utilities/prep4html.sh < origpub.tex > origpub_html.tex

contrib_html.tex: contrib.tex
	sh utilities/prep4html.sh < contrib.tex > contrib_html.tex

perfbook_html.tex: perfbook_flat.tex qqz_html.tex origpub_html.tex contrib_html.tex perfbook.bbl
	sh utilities/prep4html.sh < perfbook_flat.tex > perfbook_html.tex
	cp perfbook.bbl perfbook_html.bbl

perfbook_html: perfbook_html.tex
	latex2html -show_section_numbers -local_icons perfbook_html

$(EPSTARGETS_OF_TEX): %.eps: %.tex
	latex -output-directory=$(shell dirname $<) $<
	dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@
	sh utilities/fixanepsfonts.sh $@

$(PDFTARGETS_OF_DOT): %.pdf: %.dot
	dot -Tpdf -o $@ $<

$(EPSTARGETS_OF_DOT): %.eps: %.dot
	dot -Tps -o $@ $<

clean:
	find . -name '*.aux' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' \
		-o -name '*.qqz' -o -name '*.toc' -o -name '*.bbl' | xargs rm -f
	rm -f perfbook_flat.tex perfbook_html.tex perfbook.out perfbook-1c.out
	rm -f perfbook-hb.out perfbook-1c.tex perfbook-hb.tex
	rm -f perfbook_aux extraction embedfonts
	rm -f perfbook-1c_aux perfbook-hb_aux
	rm -rf perfbook_html

distclean: clean
	sh utilities/cleanpdf.sh
	rm -f $(EPS_NOT_IN_REPO)

touchsvg:
	find . -name '*.svg' | xargs touch

neatfreak: distclean
	# Don't forget to regenerate the .pdf from each .svg file
	find . -name '*.pdf' | xargs rm -f
