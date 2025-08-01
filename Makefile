LATEX ?= pdflatex
WHICH = command -v

GITREFSTAGS := $(shell ls -d .git/refs/tags 2>/dev/null)

LATEXSOURCES = \
	perfbook-lt.tex \
	legal.tex \
	summary.tex \
	glossary.tex \
	qqz.sty origpub.sty \
	glsdict.tex indexsee.tex \
	pfbook.cls \
	ushyphex.tex pfhyphex.tex \
	ack.tex \
	*/*.tex \
	*/*/*.tex

LST_SOURCES := $(wildcard CodeSamples/formal/promela/*.lst) \
	$(wildcard appendix/styleguide/*.c)

SUB_QQZ := qqzhowto.tex qqzintro.tex qqzcpu.tex qqztoolsoftrade.tex \
	qqzcount.tex qqzSMPdesign.tex qqzlocking.tex qqzowned.tex \
	qqzdefer.tex qqzdatastruct.tex qqzdebugging.tex qqzformal.tex \
	qqztogether.tex	qqzadvsync.tex qqzmemorder.tex qqzeasy.tex \
	qqzfuture.tex qqzquestions.tex qqztoyrcu.tex qqzwhymb.tex

LATEXGENERATED = autodate.tex qqz.tex contrib.tex origpub.tex sub_qqz
# Note: Empty target "sub_qqz" is used on behalf of $(SUB_QQZ) to prevent
# parallel runs of divideqqz.pl.

TWOCOLTARGETS := mstx msr msn msnt sf nq sfnq ix df
EBTARGETS := $(foreach v,nq sf sfnq ix df,eb$(v))
ABBREVTARGETS := lt hb a4 1c tcb msns mss eb $(TWOCOLTARGETS) $(foreach v,$(TWOCOLTARGETS),1c$(v)) $(EBTARGETS)

PDFTARGETS := perfbook.pdf $(foreach v,$(ABBREVTARGETS),perfbook-$(v).pdf)
GENERATED_MAIN := $(filter-out perfbook-lt.tex,$(foreach v,$(ABBREVTARGETS),perfbook-$(v).tex)) perfbook.tex

EPSSOURCES_FROM_TEX := \
	SMPdesign/DiningPhilosopher5.eps \
	SMPdesign/DiningPhilosopher5TB.eps \
	SMPdesign/DiningPhilosopher4part-b.eps \
	SMPdesign/DiningPhilosopher5PEM.eps

PDFTARGETS_OF_TEX := $(EPSSOURCES_FROM_TEX:%.eps=%.pdf)

DOTSOURCES := $(wildcard */*.dot)

EPSSOURCES_FROM_DOT := $(DOTSOURCES:%.dot=%.eps)

FIGSOURCES := $(wildcard */*.fig) $(wildcard */*/*.fig)

EPSSOURCES_FROM_FIG := $(FIGSOURCES:%.fig=%.eps)

SVGSOURCES_ALL := $(wildcard */*.svg)
SVG_EMERGENCY := $(wildcard */*.svg*.svg)
SVG_GENERATED := CodeSamples/formal/data/RCU-test-ratio.svg
SVGSOURCES := $(filter-out $(SVG_EMERGENCY) $(SVG_GENERATED),$(SVGSOURCES_ALL)) $(SVG_GENERATED)
FAKE_EPS_FROM_SVG := $(SVGSOURCES:%.svg=%.eps)
PDFTARGETS_OF_SVG := $(SVGSOURCES:%.svg=%.pdf)
PDFTARGETS_OF_SVG_CROP := CodeSamples/formal/data/RCU-test-ratio-crop.pdf

OBSOLETE_FILES = extraction $(FAKE_EPS_FROM_SVG) CodeSamples/snippets.mk

EPSSOURCES_DUP := \
	$(wildcard */*.eps) \
	$(wildcard */*/*.eps) \
	$(wildcard */*/*/*.eps) \
	$(wildcard */*/*/*/*.eps) \
	$(wildcard */*/*/*/*/*.eps) \
	$(EPSSOURCES_FROM_TEX) \
	$(EPSSOURCES_FROM_DOT) \
	$(EPSSOURCES_FROM_FIG)

EPSSOURCES_TMP := \
	$(wildcard */*__.eps) \
	$(wildcard */*/*__.eps) \
	$(wildcard */*/*/*__.eps) \
	$(wildcard */*/*/*/*__.eps) \
	$(wildcard */*/*/*/*/*__.eps) \

EPSSOURCES_OLD := \
	$(wildcard CodeSamples/*/*/OLD-*/*.eps) \
	$(wildcard CodeSamples/*/*/OLD-*/*/*.eps) \
	$(wildcard CodeSamples/*/*/*/OLD-*/*.eps) \
	$(wildcard CodeSamples/*/*/*/OLD-*/*/*.eps)

EPSSOURCES := $(sort $(filter-out $(EPSSOURCES_OLD) $(OBSOLETE_FILES) $(EPSSOURCES_TMP),$(EPSSOURCES_DUP)))

PDFTARGETS_OF_EPS := $(EPSSOURCES:%.eps=%.pdf)

EPSORIGIN := $(filter-out $(EPSSOURCES_FROM_TEX) $(EPSSOURCES_FROM_DOT) $(EPSSOURCES_FROM_FIG),$(EPSSOURCES))

GNUPLOT_ORIG := $(shell grep -l gnuplot $(EPSORIGIN))
GNUPLOT_ORIG_NOFIXFONTS := $(shell grep -l '/FontMatrix' $(GNUPLOT_ORIG))
GNUPLOT_ORIG_NEEDFIXFONTS := $(filter-out $(GNUPLOT_ORIG_NOFIXFONTS),$(GNUPLOT_ORIG))
EPSORIG_NOFIXFONTS := $(filter-out $(GNUPLOT_ORIG_NEEDFIXFONTS),$(EPSORIGIN))

PDFTARGETS_OF_EPSORIG := $(EPSORIGIN:%.eps=%.pdf)
PDFTARGETS_OF_GNUPLOT_NEEDFIXFONTS := $(GNUPLOT_ORIG_NEEDFIXFONTS:%.eps=%.pdf)
PDFTARGETS_OF_EPSORIG_NOFIXFONTS := $(EPSORIG_NOFIXFONTS:%.eps=%.pdf)

PDFTARGETS_OF_EPSOTHER := $(filter-out $(PDFTARGETS_OF_EPSORIG) $(PDFTARGETS_OF_TEX),$(PDFTARGETS_OF_EPS))

BIBSOURCES := bib/*.bib alphapf.bst

# required commands
SED ?= sed

LATEX_CMD := $(shell $(WHICH) $(LATEX) 2>/dev/null)
DOT := $(shell $(WHICH) dot 2>/dev/null)
FIG2EPS := $(shell $(WHICH) fig2eps 2>/dev/null)
FIG2DEV := $(shell $(WHICH) fig2dev 2>/dev/null)
INKSCAPE := $(shell $(WHICH) inkscape 2>/dev/null)
ifdef INKSCAPE
  INKSCAPE_ONE := $(shell inkscape --version 2>/dev/null | grep -c "Inkscape 1")
endif
# rsvg-convert is preferred to inkscape in SVG --> PDF conversion
RSVG_CONVERT := $(shell $(WHICH) rsvg-convert 2>/dev/null)
ifdef RSVG_CONVERT
  RSVG_CONVERT_VER := $(shell rsvg-convert --version | $(SED) -e 's/rsvg-convert version //')
  RSVG_CONVERT_VER_MINOR := $(shell echo $(RSVG_CONVERT_VER) | $(SED) -E -e 's/^([0-9]+\.[0-9]+).*/\1/')
  RSVG_CONVERT_GOOD_VER ?= 2.57
  RSVG_CONVERT_PDFFMT_VER := 2.57
  RSVG_CONVERT_ACCEPTABLE_VER := 2.52
  RSVG_CONVERT_GOOD := $(shell echo $(RSVG_CONVERT_VER_MINOR) $(RSVG_CONVERT_GOOD_VER) | awk '{if ($$1 >= $$2) print 1;}')
  RSVG_CONVERT_ACCEPTABLE := $(shell echo $(RSVG_CONVERT_VER_MINOR) $(RSVG_CONVERT_ACCEPTABLE_VER) | awk '{if ($$1 == $$2) print 1;}')
  ifeq ($(RSVG_CONVERT_ACCEPTABLE),1)
    RSVG_CONVERT_GOOD := 1
  endif
  ifndef INKSCAPE
    RSVG_CONVERT_GOOD := 1
  endif
  RSVG_CONVERT_PDFFMT := $(shell echo $(RSVG_CONVERT_VER_MINOR) $(RSVG_CONVERT_PDFFMT_VER) | awk '{if ($$1 >= $$2) print 1;}')
  ifeq ($(RSVG_CONVERT_GOOD),1)
    SVG_PDF_CONVERTER = (rsvg-convert v$(RSVG_CONVERT_VER))
  else
    SVG_PDF_CONVERTER = (inkscape)
  endif
  ifeq ($(RSVG_CONVERT_PDFFMT),1)
    RSVG_FMT_OPT := --format=pdf1.5
  else
    RSVG_FMT_OPT := --format=pdf
  endif
else
  SVG_PDF_CONVERTER = (inkscape)
endif
LATEXPAND := $(shell $(WHICH) latexpand 2>/dev/null)
QPDF := $(shell $(WHICH) qpdf 2>/dev/null)
GNUPLOT := $(shell $(WHICH) gnuplot 2>/dev/null)

# required fonts
STEELFONT := $(shell fc-list | grep -c -i steel)
URWPS := $(shell fc-list | grep "Nimbus Mono PS" | wc -l)

# required font packages
FONTPACKAGES := $(shell kpsewhich newtxtext.sty nimbusmono.sty newtxtt.sty newtxsf.sty inconsolata.sty couriers.sty)
NEWTXTEXT := $(findstring newtxtext,$(FONTPACKAGES))
NIMBUSMONO := $(findstring nimbusmono,$(FONTPACKAGES))
NEWTXTT := $(findstring newtxtt,$(FONTPACKAGES))
COURIERS := $(findstring couriers,$(FONTPACKAGES))
NEWTXSF := $(findstring newtxsf,$(FONTPACKAGES))
INCONSOLATA := $(findstring inconsolata,$(FONTPACKAGES))
FREESANS := $(shell fc-list | grep FreeSans | wc -l)
DEJAVUSANS := $(shell fc-list | grep "DejaVu Sans" | grep -v "DejaVu Sans Mono" | wc -l)
DEJAVUMONO := $(shell fc-list | grep "DejaVu Sans Mono" | wc -l)
LIBERATIONSANS := $(shell fc-list | grep "Liberation Sans" | wc -l)
LIBERATINOMONO := $(shell fc-list | grep "Liberation Mono" | wc -l)

# for line break in error text
define n


endef

ifeq ($(URWPS),0)
FIXSVGFONTS   = utilities/fixsvgfonts.sh
FIXANEPSFONTS = utilities/fixanepsfonts.sh
FIXFONTS      = utilities/fixfonts.sh
else
FIXSVGFONTS   = utilities/fixsvgfonts-urwps.sh
FIXANEPSFONTS = utilities/fixanepsfonts-urwps.sh
FIXFONTS      = utilities/fixfonts-urwps.sh
endif
ifeq ($(FREESANS),0)
  RECOMMEND_FREEFONT := 1
else
  RECOMMEND_FREEFONT := 0
endif
ifeq ($(DEJAVUSANS),0)
  RECOMMEND_DEJAVUSANS := 1
else
  RECOMMEND_DEJAVUSANS := 0
endif
ifeq ($(DEJAVUMONO),0)
  RECOMMEND_DEJAVUMONO := 1
else
  RECOMMEND_DEJAVUMONO := 0
endif
ifeq ($(LIBERATIONSANS),0)
  RECOMMEND_LIBERATIONSANS := 1
else
  RECOMMEND_LIBERATIONSANS := 0
endif
ifeq ($(LIBERATIONMONO),0)
  RECOMMEND_LIBERATIONMONO := 1
else
  RECOMMEND_LIBERATIONMONO := 0
endif


STEELFONTID := $(shell fc-list | grep -i steel | grep -c Steel)

LINELABEL_ENV_BEGIN := $(shell grep -l -F '\begin{linelabel}' $(LATEXSOURCES))
LINELABEL_ENV_END   := $(shell grep -l -F '\end{linelabel}'   $(LATEXSOURCES))
LINEREF_ENV_BEGIN   := $(shell grep -l -F '\begin{lineref}'   $(LATEXSOURCES))
LINEREF_ENV_END     := $(shell grep -l -F '\end{lineref}'     $(LATEXSOURCES))
LINELABEL_ENV := $(sort $(LINELABEL_ENV_BEGIN) $(LINELABEL_ENV_END))
LINEREF_ENV   := $(sort $(LINEREF_ENV_BEGIN) $(LINEREF_ENV_END))

SOURCES_OF_SNIPPET_ALL := $(shell grep -r -l -F '\begin{snippet}' CodeSamples)
SOURCES_OF_LITMUS      := $(shell grep -r -l -F '\begin[snippet]' CodeSamples)
SOURCES_OF_LTMS        := $(patsubst %.litmus,%.ltms,$(SOURCES_OF_LITMUS))
SOURCES_OF_SNIPPET     := $(filter-out $(SOURCES_OF_LTMS),$(SOURCES_OF_SNIPPET_ALL)) $(SOURCES_OF_LITMUS)
GEN_SNIPPET_D  = utilities/gen_snippet_d.pl utilities/gen_snippet_d.sh utilities/precheck.sh

default = $(PERFBOOK_DEFAULT)

ifeq ($(default),)
	targ = perfbook.pdf
else
	targ = $(default)
endif

chkpagegroup = $(PERFBOOK_CHKPAGEGROUP)

ifeq ($(PERFBOOK_PAPER),A4)
	PERFBOOK_BASE = perfbook-a4.tex
else
ifeq ($(PERFBOOK_PAPER),HB)
	PERFBOOK_BASE = perfbook-hb.tex
else
	PERFBOOK_BASE = perfbook-lt.tex
endif
endif

BASE_DEPENDS := perfbook.tex $(foreach v,tcb 1c msns mss mstx msr msn msnt sf nq ix df,perfbook-$(v).tex)

.PHONY: all touchsvg clean distclean neatfreak 2c ls-unused $(ABBREVTARGETS)
.PHONY: mslm perfbook-mslm.pdf mslmmsg
.PHONY: qq perfbook-qq.pdf qqmsg
.PHONY: help help-official help-full help-semiofficial help-paper help-draft
.PHONY: help-experimental help-prefixed
.PHONY: paper-clean periodcheck punctcheck punctcheck-auto
.PHONY: cleanfigs cleanfigs-eps cleanfigs-svg figs precheck

all: punctcheck-auto

ifeq ($(MAKECMDGOALS),clean)
else ifeq ($(MAKECMDGOALS),distclean)
else ifeq ($(MAKECMDGOALS),neatfreak)
else ifeq ($(MAKECMDGOALS),precheck)
else
  include CodeSamples/snippets.d
endif

2c: perfbook.pdf

mslm: perfbook-mslm.pdf
perfbook-mslm.pdf: mslmmsg

qq: perfbook-qq.pdf
perfbook-qq.pdf: qqmsg

mslmmsg: perfbook.pdf
	@echo "perfbook-mslm.pdf is promoted to default target,"
	@echo "built as perfbook.pdf."

qqmsg: perfbook.pdf
	@echo "perfbook-qq.pdf is promoted to default target,"
	@echo "built as perfbook.pdf."

$(PDFTARGETS): %.pdf: %.tex %.bbl
ifeq ($(LATEX_CMD),)
	$(error LaTeX engine "$(LATEX)" not found.)
endif
	LATEX=$(LATEX) sh utilities/runlatex.sh $(basename $@)

$(PDFTARGETS:.pdf=.bbl): %.bbl: %.aux $(BIBSOURCES)
	bibtex $(basename $@)

$(PDFTARGETS:.pdf=.aux): %.aux: %.tex $(LATEXGENERATED)
ifeq ($(NEWTXTEXT),)
	$(error Font package 'newtx' not found. See #9 in FAQ-BUILD.txt)
endif
ifeq ($(LATEX_CMD),)
	$(error LaTeX engine "$(LATEX)" not found.)
endif
	LATEX=$(LATEX) sh utilities/runfirstlatex.sh $(basename $@)

autodate.tex: $(LATEXSOURCES) $(BIBSOURCES) $(LST_SOURCES) \
    $(PDFTARGETS_OF_EPS) $(PDFTARGETS_OF_SVG) $(PDFTARGETS_OF_SVG_CROP) \
    $(FCVSNIPPETS) $(FCVSNIPPETS_VIA_LTMS) \
    $(GITREFSTAGS) utilities/autodate.sh
	sh utilities/autodate.sh

perfbook_flat.tex: autodate.tex
ifndef LATEXPAND
	$(error --> $@: latexpand not found. Please install it)
endif
	@if [ ! -z "$(LINELABEL_ENV)" -a "$(LINELABEL_ENV)" != " " ]; then \
		echo "'linelabel' used as environment in $(LINELABEL_ENV)." ; \
		echo "------" ; \
		grep -n -B 2 -A 2 -F 'linelabel' $(LINELABEL_ENV) ; \
		echo "------" ; \
		echo "Substitute 'fcvlabel' for 'linelabel' in $(LINELABEL_ENV)." ; \
		exit 1 ; \
	fi
	@if [ ! -z "$(LINEREF_ENV)" -a "$(LINEREF_ENV)" != " " ]; then \
		echo "'lineref' used as environment in $(LINEREF_ENV)." ; \
		echo "------" ; \
		grep -n -B 2 -A 2 -F 'lineref' $(LINEREF_ENV) ; \
		echo "------" ; \
		echo "Substitute 'fcvref' for 'lineref' in $(LINEREF_ENV)." ; \
		exit 1 ; \
	fi
	echo > qqz.tex
	echo > contrib.tex
	echo > origpub.tex
	latexpand --empty-comments perfbook-lt.tex 1> $@ 2> /dev/null

qqz.tex: perfbook_flat.tex
	sh utilities/extractqqz.sh < $< | perl utilities/qqzreorder.pl > $@

contrib.tex: perfbook_flat.tex qqz.tex
	cat $^ | sh utilities/extractcontrib.sh > $@

origpub.tex: perfbook_flat.tex
	sh utilities/extractorigpub.sh < $< > $@

# Empty target to generate $(SUB_QQZ) files
sub_qqz: qqz.tex
	utilities/divideqqz.pl
	@touch sub_qqz

perfbook.tex: $(PERFBOOK_BASE)
	cp $< $@

perfbook-tcb.tex: $(PERFBOOK_BASE)
	sed -e 's/{tblcptop}{true}/{tblcptop}{false}/' < $< > $@

perfbook-1c.tex: $(PERFBOOK_BASE)
	sed -e 's/setboolean{twocolumn}{true}/setboolean{twocolumn}{false}/' < $< > $@

perfbook-hb.tex: perfbook-lt.tex
	sed -e 's/setboolean{hardcover}{false}/setboolean{hardcover}{true}/' < $< > $@

perfbook-eb.tex: perfbook-lt.tex
	sed -e 's/setboolean{ebooksize}{false}/setboolean{ebooksize}{true}/' \
	    -e 's/setboolean{twocolumn}{true}/setboolean{twocolumn}{false}/' < $< > $@

perfbook-msns.tex: $(PERFBOOK_BASE)
	sed -e 's/%msfontstub/\\usepackage{courier}/' < $< > $@

perfbook-mss.tex: $(PERFBOOK_BASE)
ifeq ($(COURIERS),)
	$(error Font package 'courier-scaled' not found. See #9 in FAQ-BUILD.txt)
endif
	sed -e 's/%msfontstub/\\usepackage[scaled=.94]{couriers}/' < $< > $@

perfbook-mstx.tex: $(PERFBOOK_BASE)
perfbook-1cmstx.tex: perfbook-1c.tex
perfbook-mstx.tex perfbook-1cmstx.tex:
	sed -e 's/%msfontstub/\\renewcommand*\\ttdefault{txtt}/' < $< > $@

perfbook-msr.tex: $(PERFBOOK_BASE)
perfbook-1cmsr.tex: perfbook-1c.tex
perfbook-msr.tex perfbook-1cmsr.tex:
ifeq ($(NIMBUSMONO),)
	$(error Font package 'nimbus15' not found. See #9 in FAQ-BUILD.txt)
endif
	sed -e 's/%msfontstub/\\usepackage[scaled=.94]{nimbusmono}/' \
	    -e 's/{nimbusavail}{false}/{nimbusavail}{true}/' < $< > $@

perfbook-msn.tex: $(PERFBOOK_BASE)
perfbook-1cmsn.tex: perfbook-1c.tex
perfbook-msn.tex perfbook-1cmsn.tex:
ifeq ($(NIMBUSMONO),)
	$(error Font package 'nimbus15' not found. See #9 in FAQ-BUILD.txt)
endif
	sed -e 's/\\renewcommand\*\\ttdefault{lmtt}//' \
	    -e 's/{lmttforcode}{true}/{lmttforcode}{false}/' \
	    -e 's/{nimbusavail}{false}/{nimbusavail}{true}/' < $< > $@

perfbook-msnt.tex: $(PERFBOOK_BASE)
perfbook-1cmsnt.tex: perfbook-1c.tex
perfbook-msnt.tex perfbook-1cmsnt.tex:
ifeq ($(NEWTXTT),)
	$(error Font package 'newtxtt' not found.$nInstall it or try 'make mstx' instead. See #9 in FAQ-BUILD.txt)
endif
ifeq ($(NIMBUSMONO),)
	$(error Font package 'nimbus15' not found. See #9 in FAQ-BUILD.txt)
endif
	sed -e 's/%msfontstub/\\usepackage[zerostyle=a]{newtxtt}/' \
	    -e 's/{qqzbg}{false}/{qqzbg}{true}/' \
	    -e 's/{nimbusavail}{false}/{nimbusavail}{true}/' < $< > $@

perfbook-sf.tex: $(PERFBOOK_BASE)
perfbook-1csf.tex: perfbook-1c.tex
perfbook-ebsf.tex: perfbook-eb.tex
perfbook-sf.tex perfbook-1csf.tex perfbook-ebsf.tex:
ifeq ($(NEWTXSF),)
	$(error Font package 'newtxsf' not found. See #9 in FAQ-BUILD.txt)
endif
ifeq ($(INCONSOLATA),)
	$(error Font package 'inconsolata' not found. See #9 in FAQ-BUILD.txt)
endif
ifeq ($(NIMBUSMONO),)
	$(error Font package 'nimbus15' not found. See #9 in FAQ-BUILD.txt)
endif
	sed -e 's/setboolean{sansserif}{false}/setboolean{sansserif}{true}/' \
	    -e 's/{nimbusavail}{false}/{nimbusavail}{true}/' \
	    -e 's/%msfontstub/\\usepackage[var0]{inconsolata}[2013\/07\/17]/' < $< > $@

perfbook-nq.tex: $(PERFBOOK_BASE)
perfbook-sfnq.tex: perfbook-sf.tex
perfbook-1cnq.tex: perfbook-1c.tex
perfbook-1csfnq.tex: perfbook-1csf.tex
perfbook-ebnq.tex: perfbook-eb.tex
perfbook-ebsfnq.tex: perfbook-ebsf.tex
perfbook-nq.tex perfbook-sfnq.tex perfbook-1cnq.tex perfbook-1csfnq.tex perfbook-ebnq.tex perfbook-ebsfnq.tex:
	sed -e 's/setboolean{qqzbg}{true}/setboolean{qqzbg}{false}/' \
	    -e 's/setboolean{noqqz}{false}/setboolean{noqqz}{true}/' < $< > $@

perfbook-ix.tex: $(PERFBOOK_BASE)
perfbook-1cix.tex: perfbook-1c.tex
perfbook-ebix.tex: perfbook-eb.tex
perfbook-ix.tex perfbook-1cix.tex perfbook-ebix.tex:
	sed -e 's/setboolean{qqzbg}{true}/setboolean{qqzbg}{false}/' \
	    -e 's/setboolean{indexhl}{false}/setboolean{indexhl}{true}/' < $< > $@

perfbook-df.tex: $(PERFBOOK_BASE)
perfbook-1cdf.tex: perfbook-1c.tex
perfbook-ebdf.tex: perfbook-eb.tex
perfbook-df.tex perfbook-1cdf.tex perfbook-ebdf.tex:
	sed -e 's/setboolean{qqzbg}{true}/setboolean{qqzbg}{false}/' \
	    -e 's/setboolean{indexon}{true}/setboolean{indexon}{false}/' < $< > $@

perfbook-a4.tex: perfbook-lt.tex
perfbook-a4.tex:
	sed -e 's/{afourpaper}{false}/{afourpaper}{true}/' < $< > $@

# Rules related to perfbook_html are removed as of May, 2016

$(EPSSOURCES_FROM_TEX): %.eps: %.tex
	@echo "$< --> $(suffix $@)"
	sh utilities/mpostcheck.sh
	@latex -output-directory=$(shell dirname $<) $< > /dev/null 2>&1
	@dvips -Pdownload35 -E $(patsubst %.tex,%.dvi,$<) -o $@ > /dev/null 2>&1

$(EPSSOURCES_FROM_DOT): $(FIXANEPSFONTS) $(FIXFONTS)
$(EPSSOURCES_FROM_DOT): %.eps: %.dot
	@echo "$< --> $(suffix $@)"
ifndef DOT
	$(error $< --> $@: dot not found. Please install graphviz)
endif
	@dot -Tps -o $@ $<
	@sh $(FIXANEPSFONTS) $@

$(EPSSOURCES_FROM_FIG): $(FIXANEPSFONTS) $(FIXFONTS)
$(EPSSOURCES_FROM_FIG): %.eps: %.fig
	@echo "$< --> $(suffix $@)"
ifdef FIG2EPS
	@fig2eps --nogv $< > /dev/null 2>&1
else ifdef FIG2DEV
	@fig2dev -L eps $< $@
else
	$(error $< --> $@: Neither fig2eps nor fig2dev found. Please install fig2ps or transfig (or fig2dev))
endif
	@sh $(FIXANEPSFONTS) $@

# .eps --> .pdf rules
ifdef USE_A2PING
  include a2ping-rule.mk
else
  include epstopdf-rule.mk
endif

# bogus settings for preventing Inkscape from interacting with desktop manager
ISOLATE_INKSCAPE ?= XDG_RUNTIME_DIR=na DBUS_SESSION_BUS_ADDRESS=na

CodeSamples/formal/data/RCU-test-ratio.svg: CodeSamples/formal/data/rcu-test.dat
CodeSamples/formal/data/RCU-test-ratio.svg: CodeSamples/formal/data/plot.sh
CodeSamples/formal/data/RCU-test-ratio.svg:
	@echo "Generating $@"
ifndef GNUPLOT
	$(error gnuplot not found. Please install it)
endif
	@cd CodeSamples/formal/data/ && \
	    sh plot.sh && \
	    cd ../../..

$(PDFTARGETS_OF_SVG_CROP): %-crop.pdf: %.pdf
	@echo "Crop $< (pdfcrop)"
	@pdfcrop $< $@ > /dev/null

ifdef RSVG_CONVERT
  FALLBACK_RSVG_CONVERT = || (cat $<i | rsvg-convert $(RSVG_FMT_OPT) > $@ && echo "$< --> $(suffix $@) (fallback rsvg-convert)")
endif
ifeq ($(RSVG_CONVERT_GOOD),1)
  SVG_TO_PDF_COMMAND = cat $<i | rsvg-convert $(RSVG_FMT_OPT) > $@
else
  ifeq ($(INKSCAPE_ONE),0)
    SVG_TO_PDF_COMMAND = inkscape --export-pdf=$@ $<i > /dev/null 2>&1 $(FALLBACK_RSVG_CONVERT)
  else
    SVG_TO_PDF_COMMAND = $(ISOLATE_INKSCAPE) inkscape -o $@ $<i > /dev/null 2>&1 $(FALLBACK_RSVG_CONVERT)
  endif
endif

$(PDFTARGETS_OF_SVG): $(FIXSVGFONTS)
$(PDFTARGETS_OF_SVG): %.pdf: %.svg
	@echo "$< --> $(suffix $@) $(SVG_PDF_CONVERTER)"
ifeq ($(STEELFONT),0)
	$(error "Steel City Comic" font not found. See #1 in FAQ.txt)
endif
ifneq ($(RSVG_CONVERT_GOOD),1)
  ifndef INKSCAPE
	$(error $< --> $@ inkscape nor rsvg-convert not found. Please install either one)
  endif
endif
ifeq ($(STEELFONTID),0)
	@sh $(FIXSVGFONTS) < $< | sed -e 's/Steel City Comic/Test/g' > $<i
else
	@sh $(FIXSVGFONTS) < $< > $<i
endif
ifeq ($(RECOMMEND_FREEFONT),1)
	$(info Nice-to-have font family 'FreeMono' not found. See #9 in FAQ-BUILD.txt)
endif
ifeq ($(RECOMMEND_DEJAVUSANS),1)
	$(info Nice-to-have font family 'DejaVu Sans' not found. See #9 in FAQ-BUILD.txt)
endif
ifeq ($(RECOMMEND_DEJAVUMONO),1)
	$(info Nice-to-have font family 'DejaVu Sans Mono' not found. See #9 in FAQ-BUILD.txt)
endif
ifeq ($(RECOMMEND_LIBERATIONSANS),1)
	$(info Nice-to-have font family 'Liberation Sans' not found. See #9 in FAQ-BUILD.txt)
endif
ifeq ($(RECOMMEND_LIBERATIONMONO),1)
	$(info Nice-to-have font family 'Liberation Mono' not found. See #9 in FAQ-BUILD.txt)
endif
	@$(SVG_TO_PDF_COMMAND)
	@rm -f $<i
ifeq ($(chkpagegroup),on)
ifndef QPDF
	$(error qpdf not found. Please install it)
endif
	@echo "checking page group in $@"
	@qpdf --qdf $@ $@q
	@./utilities/extpagegroup.pl < $@q > $@p
	@diff -q -w $@p pagegroup
	@rm -f $@q $@p
endif

CodeSamples/snippets.d: $(SOURCES_OF_SNIPPET) $(GEN_SNIPPET_D)
	sh ./utilities/precheck.sh
	sh ./utilities/gen_snippet_d.sh

$(FCVSNIPPETS):
	@echo "$< --> $(suffix $@)"
	@utilities/fcvextract.pl $< $(subst +,\\+,$(subst @,:,$(basename $(notdir $@)))) > $@
	@utilities/checkfcv.pl $@

$(FCVSNIPPETS_VIA_LTMS):
	@echo "$< --> $(suffix $@)"
	@utilities/fcvextract.pl $< $(subst +,\\+,$(subst @,:,$(basename $(notdir $@)))) > $@
	@utilities/checkfcv.pl $@

$(FCVSNIPPETS_LTMS):
	@echo "$< --> $(suffix $@)"
	@utilities/reorder_ltms.pl $< > $@

help-official:
	@echo "Official targets (Latin Modern Typewriter for monospace font):"
	@echo "  Full,              Abbr."
	@echo "  perfbook.pdf,      2c:   (default) 2-column layout"
	@echo "  perfbook-1c.pdf,   1c:   1-column layout"
	@echo "Note:"
	@echo "  Official targets now enable indexing and Quick-Quiz framing."

help-semiofficial:
	@echo
	@echo "Semi-official targets:"
	@echo "  Full,              Abbr."
	@echo "  perfbook-nq.pdf,   nq:   2c without inline Quick Quizzes (chapterwise Qs)"
	@echo "  perfbook-sf.pdf,   sf:   2c with sans serif font"
	@echo "  perfbook-sfnq.pdf, sfnq: sf + nq"

help-paper:
	@echo
	@echo "Set env variable PERFBOOK_PAPER to change paper size:"
	@echo "   PERFBOOK_PAPER=A4: a4paper"
	@echo "   PERFBOOK_PAPER=HB: hard cover book"
	@echo "   other (default):   letterpaper"
	@echo "Note:"
	@echo "  Modified PERFBOOK_PAPER takes effect after \"make paper-clean\"."
	@echo
	@echo "Paper-size specific targets (independent of PERFBOOK_PAPER):"
	@echo "  perfbook-lt.pdf,   lt:   2c layout on letterpaper"
	@echo "  perfbook-hb.pdf,   hb:   2c layout for hard cover book"
	@echo "  perfbook-a4.pdf,   a4:   2c layout on a4paper"
	@echo "  perfbook-eb.pdf,   eb:   1c layout for ebook reader"

help: help-official help-paper
	@echo
	@echo "\"make help-full\" will show the full list of available targets."

help-draft:
	@echo
	@echo "Targets for draft check, non-framed Quick Quizzes (quicker build)"
	@echo "  perfbook-ix.pdf,   ix:   for draft check, with indexed terms highlighted"
	@echo "  perfbook-df.pdf,   df:   for draft check, without indexing"

help-prefixed:
	@echo
	@echo "Prefixed targets:"
	@echo "  \"1c*\" such as \"1cnq\", \"1csf\", and \"1cix\" are for 1c-layout."
	@echo "  \"ebnq\", \"ebsf\", \"ebsfnq\", \"ebix\", and \"ebdf\" are for ebook-size 1c-layout,"
	@echo "     independent of PERFBOOK_PAPER."

help-experimental:
	@echo
	@echo "Experimental targets:"
	@echo "  perfbook-msnt.pdf, msnt: newtxtt as monospace (non-slashed 0)"
	@echo "  perfbook-mstx.pdf, mstx: txtt as monospace"
	@echo "  perfbook-msr.pdf,  msr:  regular thickness courier clone as monospace"
	@echo "  perfbook-msn.pdf,  msn:  narrow courier clone as monospace"
	@echo
	@echo "Historical targets:"
	@echo "  perfbook-tcb.pdf,  tcb:  table caption at bottom (First Edition)"
	@echo "  perfbook-msns.pdf, msns: non-scaled courier (First Edition)"
	@echo "  perfbook-mss.pdf,  mss:  scaled courier (default in early 2017)"
	@echo
	@echo "Notes:"
	@echo "  - \"msnt\" requires \"newtxtt\". \"mstx\" is a fallback target for older TeX env."
	@echo "  - \"msr\" and \"msn\" require \"nimbus15\"."
	@echo "  - \"msn\" doesn't cover bold face monospace."
	@echo "  - \"sf\" requires \"newtxsf\"."
	@echo "  - All the targets except for \"msn\" use \"Latin Modern Typewriter\" font"
	@echo "    for code snippets."

help-full: help-official help-paper help-semiofficial help-draft help-prefixed help-experimental

clean:
	find . -name '*.aux' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' \
		-o -name '*.qqz' -o -name '*.toc' -o -name '*.bbl' \
		-o -name '*.pdfp' -o -name '*.pdfq' | xargs rm -f
	rm -f perfbook_flat.tex perfbook*.out $(GENERATED_MAIN)
	rm -f $(LATEXGENERATED)
	rm -f qqz*.tex
	rm -f perfbook*.idx perfbook*.ind perfbook*.ilg perfbook*.ist
	rm -f perfbook*.acn perfbook*.acr perfbook*.alg
	rm -f perfbook*.glg perfbook*.glo perfbook*.gls perfbook*.glsdefs
	rm -f perfbook*.sil
	rm -f CodeSamples/snippets.d
	rm -f *.synctex*
	@rm -f $(OBSOLETE_FILES) $(EPSSOURCES_TMP) $(SVG_EMERGENCY)

paper-clean:
	rm -f $(BASE_DEPENDS)

distclean: clean
	sh utilities/cleanpdf.sh
	rm -f $(EPSSOURCES_FROM_DOT) $(EPSSOURCES_FROM_TEX) $(EPSSOURCES_FROM_FIG)
	find . -name '*.fcv' -o -name '*.ltms' | xargs rm -f

touchsvg:
	find . -name '*.svg' | xargs touch

ls-unused:
	find . -name .unused | xargs ls

neatfreak: distclean
	find . -name '*.pdf' | xargs rm -f

cleanfigs-eps:
	rm -f $(EPSSOURCES_FROM_TEX) $(EPSSOURCES_FROM_DOT) $(EPSSOURCES_FROM_FIG)
	rm -f $(PDFTARGETS_OF_EPS)

cleanfigs-svg:
	rm -f $(PDFTARGETS_OF_SVG) $(SVG_EMERGENCY) $(SVG_GENERATED) $(PDFTARGETS_OF_SVG_CROP)

cleanfigs: cleanfigs-eps cleanfigs-svg

figs: $(PDFTARGETS_OF_EPS) $(PDFTARGETS_OF_SVG) $(PDFTARGETS_OF_SVG_CROP)

punctcheck:
	utilities/punctcheck.sh
	utilities/cleverefcheck.sh

punctcheck-auto: $(targ)
	utilities/punctcheck.sh
	utilities/cleverefcheck.sh

precheck:
	VERBOSE=y sh utilities/precheck.sh

periodcheck: punctcheck

.SECONDEXPANSION:
$(ABBREVTARGETS): %: perfbook-$$@.pdf
