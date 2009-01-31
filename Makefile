LATEXSOURCES = \
	perfbook.tex \
	ack.tex \
	legal.tex \
	preface.tex \
	qqz.sty origpub.sty \
	advsync/advsync.tex \
	advsync/memorybarriers.tex \
	analysis/analysis.tex \
	appendix/appendix.tex \
	appendix/ack/ack.tex \
	appendix/formal/formal.tex \
	appendix/formal/spinhint.tex \
	appendix/formal/dyntickrcu.tex \
	appendix/primitives/primitives.tex \
	appendix/questions/after.tex \
	appendix/questions/questions.tex \
	appendix/rcuimpl/rcu.tex \
	appendix/rcuimpl/srcu.tex \
	appendix/rcuimpl/rcutree.tex \
	appendix/rcuimpl/rcutreewt.tex \
	appendix/rcuimpl/rcupreempt.tex \
	appendix/whymb/whymemorybarriers.tex \
	cpu/cpu.tex \
	cpu/overview.tex \
	cpu/overheads.tex \
	cpu/hwfreelunch.tex \
	cpu/swdesign.tex \
	datastruct/datastruct.tex \
	debugging/debugging.tex \
	easy/easy.tex \
	glossary.tex \
	intro/intro.tex \
	memalloc/memalloc.tex \
	owned/owned.tex \
	defer/defer.tex \
	defer/refcnt.tex \
	defer/rcu.tex \
	defer/rcufundamental.tex \
	defer/rcuapi.tex \
	defer/rcuusage.tex \
	defer/toyrcu.tex \
	SMPdesign/SMPdesign.tex \
	SMPdesign/partexercises.tex \
	SMPdesign/criteria.tex \
	stats/stats.tex \
	locking/locking.tex \
	time/time.tex

EPSSOURCES = \
	SMPdesign/AllocatorPool.eps \
	SMPdesign/DiningPhilosopher4.eps \
	SMPdesign/DiningPhilosopher4part.eps \
	SMPdesign/DiningPhilosopher4PEM.eps \
	SMPdesign/DiningPhilosopher4TB.eps \
	SMPdesign/LockGranularity.eps \
	SMPdesign/MemoryBarrierPairing.eps \
	SMPdesign/ParallelFastpath.eps \
	SMPdesign/allocatorcache.eps \
	SMPdesign/clockfreq.eps \
	SMPdesign/lockdeq.eps \
	SMPdesign/lockdeqhash.eps \
	SMPdesign/lockdeqhash1R.eps \
	SMPdesign/lockdeqpair.eps \
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
	appendix/rcuimpl/AdvanceRCUCallbacks.eps \
	appendix/rcuimpl/BigTreeClassicRCUBHdyntick.eps \
	appendix/rcuimpl/BigTreeClassicRCUBH.eps \
	appendix/rcuimpl/BigTreeClassicRCU.eps \
	appendix/rcuimpl/FlatClassicRCU.eps \
	appendix/rcuimpl/GenericRCUStateMachine.eps \
	appendix/rcuimpl/GracePeriodBad.eps \
	appendix/rcuimpl/GracePeriodGood.eps \
	appendix/rcuimpl/RCUbweBlock.eps \
	appendix/rcuimpl/RCUpreemptCounterFlip.eps \
	appendix/rcuimpl/RCUpreemptListsCompare.eps \
	appendix/rcuimpl/RCUpreemptLists.eps \
	appendix/rcuimpl/RCUpreemptStates.eps \
	appendix/rcuimpl/RCUpreemptTimeline.eps \
	appendix/rcuimpl/RCUpreemptValidation.eps \
	appendix/rcuimpl/RCUrt-MBnowaste.eps \
	appendix/rcuimpl/RCUrt-MBwaste.eps \
	appendix/rcuimpl/RCUTreeInit.eps \
	appendix/rcuimpl/RCUTreeLeafScan.eps \
	appendix/rcuimpl/RCUTreeQSScan.eps \
	appendix/rcuimpl/srcuds.eps \
	appendix/rcuimpl/TreeClassicRCU.eps \
	appendix/rcuimpl/TreeClassicRCUGP.eps \
	appendix/rcuimpl/TreeMapping.eps \
	appendix/rcuimpl/TreeRCUStateMachine.eps \
	appendix/whymb/MESI.eps \
	appendix/whymb/cacheSB.eps \
	appendix/whymb/cacheSBf.eps \
	appendix/whymb/cacheSBfIQ.eps \
	appendix/whymb/cacheSC.eps \
	appendix/whymb/cacheSCwrite.eps \
	appendix/whymb/hostileordering.eps \
	cpu/SystemArch.eps \
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
	defer/GracePeriodGood.eps \
	defer/Linux_hlist.eps \
	defer/Linux_list_abbr.eps \
	defer/Linux_list.eps \
	defer/RCUDeletion.eps \
	defer/RCUenvAPI.eps \
	defer/RCUReplacement.eps \
	defer/refRCUperfPREEMPT.eps \
	defer/refRCUperfwtPREEMPT.eps \
	defer/rwlockRCUperf.eps \
	defer/rwlockRCUperfPREEMPT.eps \
	defer/rwlockRCUperfwtPREEMPT.eps \
	defer/rwlockRCUupdate.eps \
	easy/Mandel_zoom_00_mandelbrot_set.eps \
	intro/FourTaskCategories.eps \
	intro/Generality.eps \
	intro/PPGrelation.eps

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

perfbook.dvi: $(LATEXSOURCES) $(EPSSOURCES) qqz.tex origpub.tex
	latex perfbook || :
	test -d bib/. && bibtex perfbook || :
	latex perfbook || :
	latex perfbook || :
	latex perfbook || :

qqz.tex: $(LATEXSOURCES) $(EPSSOURCES)
	sh utilities/extractqqz.sh > qqz.tex

origpub.tex: $(LATEXSOURCES)
	sh utilities/extractorigpub.sh > origpub.tex

clean:
	find . -name '*.aux' -o -name '*.bbl' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' -o -name '*.pdf' \
		-o -name '*.qqz' -o -name '*.toc' | xargs rm
	rm -f qqz.tex
