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

EPSPDF_NOT_IN_REPO = \
	$(EPSTARGETS_OF_TEX) \
	$(PDFTARGETS_OF_DOT)

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
	$(EPSTARGETS_OF_TEX) \
	$(EPSPDF_NOT_IN_REPO)

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

.PHONY: all extraction embedfonts touchsvg clean distclean neatfreak 1c 2c hb
all: $(targ)

1c: perfbook-1c.pdf

2c: perfbook.pdf

hb: perfbook-hb.pdf

perfbook.pdf: perfbook.bbl $(LATEXSOURCES) $(EPSSOURCES) extraction embedfonts
	sh utilities/runlatex.sh perfbook

perfbook.bbl: $(BIBSOURCES) perfbook.aux
	bibtex perfbook

perfbook.aux: $(LATEXSOURCES) $(EPSSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook

perfbook_flat.tex: $(LATEXSOURCES) $(EPSSOURCES) embedfonts
	echo > qqz.tex
	texexpand perfbook.tex > perfbook_flat.tex
	sh utilities/extractqqz.sh < perfbook_flat.tex > qqz.tex

extraction: perfbook_flat.tex
	cat perfbook_flat.tex qqz.tex | sh utilities/extractcontrib.sh > contrib.tex
	sh utilities/extractorigpub.sh < perfbook_flat.tex > origpub.tex

embedfonts:
	sh utilities/fixfigfonts.sh
	sh utilities/fixdotfonts.sh
	sh utilities/eps2pdf.sh

perfbook-1c.pdf: perfbook-1c.tex perfbook-1c.bbl $(LATEXSOURCES) $(EPSSOURCES) extraction embedfonts
	sh utilities/runlatex.sh perfbook-1c

perfbook-1c.tex: perfbook.tex
	sed -e 's/,twocolumn//' -e '/^\\frontmatter/a \\\\pagestyle{plain}' -e 's/setboolean{twocolumn}{true}/setboolean{twocolumn}{false}/' < perfbook.tex > perfbook-1c.tex

perfbook-1c.bbl: $(BIBSOURCES) perfbook-1c.aux
	bibtex perfbook-1c

perfbook-1c.aux: $(LATEXSOURCES) $(EPSSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook-1c

perfbook-hb.pdf: perfbook-hb.tex perfbook-hb.bbl $(LATEXSOURCES) $(EPSSOURCES) extraction embedfonts
	sh utilities/runlatex.sh perfbook-hb

perfbook-hb.tex: perfbook.tex
	sed -e 's/,twocolumn/&,letterpaperhb/' -e 's/setboolean{hardcover}{false}/setboolean{hardcover}{true}/' < perfbook.tex > perfbook-hb.tex

perfbook-hb.bbl: $(BIBSOURCES) perfbook-hb.aux
	bibtex perfbook-hb

perfbook-hb.aux: $(LATEXSOURCES) $(EPSSOURCES) extraction embedfonts
	sh utilities/runfirstlatex.sh perfbook-hb

qqz_html.tex: perfbook_flat.tex
	sh utilities/prep4html.sh < qqz.tex > qqz_html.tex

origpub_html.tex: perfbook_flat.tex
	sh utilities/prep4html.sh < origpub.tex > origpub_html.tex

contrib_html.tex: perfbook_flat.tex
	sh utilities/prep4html.sh < contrib.tex > contrib_html.tex

perfbook_html.tex: perfbook_flat.tex qqz_html.tex origpub_html.tex contrib_html.tex perfbook.pdf
	sh utilities/prep4html.sh < perfbook_flat.tex > perfbook_html.tex
	cp perfbook.bbl perfbook_html.bbl

perfbook_html: perfbook_html.tex
	latex2html -show_section_numbers -local_icons perfbook_html

SMPdesign/DiningPhilosopher5.eps: SMPdesign/DiningPhilosopher5.tex
	latex -output-directory=$(shell dirname $<) $<
	dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@
	sh utilities/fixanepsfonts.sh SMPdesign/DiningPhilosopher5.eps

SMPdesign/DiningPhilosopher5TB.eps: SMPdesign/DiningPhilosopher5TB.tex
	latex -output-directory=$(shell dirname $<) $<
	dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@
	sh utilities/fixanepsfonts.sh SMPdesign/DiningPhilosopher5TB.eps

SMPdesign/DiningPhilosopher4part-b.eps: SMPdesign/DiningPhilosopher4part-b.tex
	latex -output-directory=$(shell dirname $<) $<
	dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@
	sh utilities/fixanepsfonts.sh SMPdesign/DiningPhilosopher4part-b.eps

SMPdesign/DiningPhilosopher5PEM.eps: SMPdesign/DiningPhilosopher5PEM.tex
	latex -output-directory=$(shell dirname $<) $<
	dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@
	sh utilities/fixanepsfonts.sh SMPdesign/DiningPhilosopher5PEM.eps

advsync/store15tred.pdf: advsync/store15tred.dot
	dot -Tpdf -o advsync/store15tred.pdf advsync/store15tred.dot

count/sig-theft.eps: count/sig-theft.dot
	dot -Tps -o count/sig-theft.eps count/sig-theft.dot

clean:
	find . -name '*.aux' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' \
		-o -name '*.qqz' -o -name '*.toc' -o -name '*.bbl' | xargs rm -f
	rm -f perfbook_flat.tex perfbook_html.tex perfbook.out perfbook-1c.out
	rm -f perfbook-hb.out perfbook-1c.tex perfbook-hb.tex
	rm -rf perfbook_html
	rm -f SMPdesign/DiningPhilosopher5.eps \
	      SMPdesign/DiningPhilosopher5TB.eps \
	      SMPdesign/DiningPhilosopher4part-b.eps \
	      SMPdesign/DiningPhilosopher5PEM.eps

distclean: clean
	sh utilities/cleanpdf.sh

touchsvg:
	find . -name '*.svg' | xargs touch

neatfreak: distclean
	# Don't forget to regenerate the .pdf from each .svg file
	find . -name '*.pdf' | xargs rm -f
