LATEXSOURCES = \
	SMPdesign/SMPdesign.tex \
	ack.tex \
	advsync/advsync.tex \
	advsync/memorybarriers.tex \
	analysis/analysis.tex \
	appendix/appendix.tex \
	appendix/formal/formal.tex \
	appendix/formal/spinhint.tex \
	appendix/formal/dyntickrcu.tex \
	appendix/primitives/primitives.tex \
	appendix/questions/after.tex \
	appendix/questions/questions.tex \
	appendix/rcuimpl/rcu.tex \
	appendix/rcuimpl/toyrcu.tex \
	appendix/rcuimpl/srcu.tex \
	appendix/rcuimpl/rcutreewt.tex \
	appendix/rcuimpl/rcupreempt.tex \
	appendix/whymb/whymemorybarriers.tex \
	cpu/cpu.tex \
	cpu/overview.tex \
	datastruct/datastruct.tex \
	debugging/debugging.tex \
	easy/easy.tex \
	glossary.tex \
	intro/intro.tex \
	legal.tex \
	memalloc/memalloc.tex \
	owned/owned.tex \
	perfbook.tex \
	preface.tex \
	defer/defer.tex \
	defer/refcnt.tex \
	defer/rcu.tex \
	defer/rcufundamental.tex \
	defer/rcuapi.tex \
	defer/rcuusage.tex \
	stats/stats.tex \
	sync/sync.tex \
	time/time.tex

EPSSOURCES = \
	SMPdesign/AllocatorPool.eps \
	SMPdesign/LockGranularity.eps \
	SMPdesign/MemoryBarrierPairing.eps \
	SMPdesign/ParallelFastpath.eps \
	SMPdesign/allocatorcache.eps \
	SMPdesign/clockfreq.eps \
	SMPdesign/smpalloc.eps \
	SMPdesign/smpalloc.old.eps \
	advsync/AbstractMemoryAccessModel.eps \
	advsync/DataDependencyNeeded.eps \
	advsync/DataDependencySupplied.eps \
	advsync/MemoryArchitecture.eps \
	advsync/MemoryBarrierPairing.eps \
	advsync/ReadBarrierNeeded.eps \
	advsync/ReadBarrierSupplied.eps \
	advsync/ReadBarrierSupplied1.eps \
	advsync/ReadBarrierSupplied2.eps \
	advsync/SpeculativeLoad.eps \
	advsync/SpeculativeLoadBarrier.eps \
	advsync/SpeculativeLoadBarrierCancel.eps \
	advsync/SplitCache.eps \
	advsync/WriteBarrierOrdering.eps \
	appendix/questions/after.eps \
	appendix/rcuimpl/srcuds.eps \
	appendix/whymb/MESI.eps \
	appendix/whymb/cacheSB.eps \
	appendix/whymb/cacheSBf.eps \
	appendix/whymb/cacheSBfIQ.eps \
	appendix/whymb/cacheSC.eps \
	appendix/whymb/cacheSCwrite.eps \
	appendix/whymb/hostileordering.eps \
	cartoons/CPU_toon_outoforder_colored.eps \
	cartoons/LD,ACQ.eps \
	cartoons/ManyFighting.eps \
	cartoons/ManyHappy.eps \
	cartoons/OldManAndBrat.eps \
	cartoons/OneFighting.eps \
	cartoons/ShavingTheMandelbrotSet.eps \
	cartoons/atomic.eps \
	cartoons/barrier.eps \
	cartoons/pipeline.eps \
	cartoons/ref.eps \
	cartoons/tollbooth.eps \
	cartoons/trackmeet.eps \
	cartoons/whippersnapper300.eps \
	cartoons/whippersnapper600.eps \
	easy/Mandel_zoom_00_mandelbrot_set.eps

all: 2up

1up: perfbook.pdf

2up: perfbook-2up.pdf

perfbook.pdf: perfbook.dvi $(EPSSOURCES)
	dvipdf perfbook

perfbook-2up.pdf: perfbook.dvi $(EPSSOURCES)
	dvips perfbook
	psnup -2 perfbook.ps perfbook-2up.ps
	ps2pdf perfbook-2up.ps perfbook-2up.pdf
	rm perfbook.ps perfbook-2up.ps

perfbook.dvi: $(LATEXSOURCES) $(EPSSOURCES) qqz.tex
	latex perfbook || :
	test -d bib/. && bibtex perfbook || :
	latex perfbook || :
	latex perfbook || :
	latex perfbook || :

qqz.tex: $(LATEXSOURCES) $(EPSSOURCES)
	sh utilities/extractqqz.sh > qqz.tex

clean:
	find . -name '*.aux' -o -name '*.bbl' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' -o -name '*.pdf' \
		-o -name '*.qqz' -o -name '*.toc' | xargs rm
	rm -f qqz.tex
