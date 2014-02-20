LATEXSOURCES = \
	perfbook.tex \
	legal.tex \
	preface.tex \
	qqz.sty origpub.sty \
	advsync/advsync.tex \
	advsync/memorybarriers.tex \
	appendix/appendix.tex \
	appendix/ack/ack.tex \
	appendix/primitives/primitives.tex \
	appendix/questions/after.tex \
	appendix/questions/time.tex \
	appendix/questions/questions.tex \
	appendix/rcuimpl/rcu.tex \
	appendix/rcuimpl/srcu.tex \
	appendix/rcuimpl/rcutree.tex \
	appendix/rcuimpl/rcutreewt.tex \
	appendix/rcuimpl/rcupreempt.tex \
	appendix/whymb/whymemorybarriers.tex \
	count/count.tex \
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
	defer/seqlock.tex \
	defer/rcu.tex \
	defer/rcuexercises.tex \
	defer/rcufundamental.tex \
	defer/rcuapi.tex \
	defer/rcuusage.tex \
	defer/toyrcu.tex \
	defer/updates.tex \
	defer/whichtochoose.tex \
	formal/formal.tex \
	formal/spinhint.tex \
	formal/dyntickrcu.tex \
	future/future.tex \
	future/cpu.tex \
	future/tm.tex \
	SMPdesign/SMPdesign.tex \
	SMPdesign/partexercises.tex \
	SMPdesign/criteria.tex \
	SMPdesign/beyond.tex \
	locking/locking.tex \
	locking/locking-existence.tex \
	together/applyrcu.tex \
	together/count.tex \
	together/hash.tex \
	together/together.tex \
	toolsoftrade/toolsoftrade.tex

EPSSOURCES = \
	SMPdesign/500-ms_2seqO3VfgO3_partO3-median.eps \
	SMPdesign/500-ms_seq_fg-cdf.eps \
	SMPdesign/500-ms_seq_fg_part-cdf.eps \
	SMPdesign/500-ms_seqO3V2seqO3_fgO3_partO3-cdf.eps \
	SMPdesign/500-ms_seqO3VfgO3_partO3-median.eps \
	SMPdesign/500-ms_seqVfg_part-cdf.eps \
	SMPdesign/500-ms_seqVfg_part_seqO3-cdf.eps \
	SMPdesign/500-pctVms_seq_part-sct.eps \
	SMPdesign/1000-ms_2seqO3VfgO3_partO3-mean.eps \
	SMPdesign/AllocatorPool.eps \
	SMPdesign/CPUvsEnet.eps \
	SMPdesign/DiningPhilosopher4.eps \
	SMPdesign/DiningPhilosopher4part.eps \
	SMPdesign/DiningPhilosopher4PEM.eps \
	SMPdesign/DiningPhilosopher4TB.eps \
	SMPdesign/LockGranularity.eps \
	SMPdesign/MazeNumberPath.eps \
	SMPdesign/MemoryBarrierPairing.eps \
	SMPdesign/ParallelFastpath.eps \
	SMPdesign/allocatorcache.eps \
	SMPdesign/clockfreq.eps \
	SMPdesign/lockdeqhash.eps \
	SMPdesign/lockdeqhash1R.eps \
	SMPdesign/lockdeqpair.eps \
	SMPdesign/matmuleff.eps \
	SMPdesign/maze_in_way10a.eps \
	SMPdesign/maze_PWQ_vs_PART.eps \
	SMPdesign/mipsperbuck.eps \
	SMPdesign/smpalloc.eps \
	SMPdesign/synceff.eps \
	SMPdesign/DiningPhilosopher5.eps \
	SMPdesign/DiningPhilosopher5TB.eps \
	SMPdesign/DiningPhilosopher4part-b.eps \
	SMPdesign/DiningPhilosopher5PEM.eps \
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
	appendix/rcuhist/linux-RCU.eps \
	appendix/rcuhist/linux-RCUlock.eps \
	appendix/rcuhist/rcuAPI.eps \
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
	cartoons/OldManAndBrat.eps \
	cartoons/ShavingTheMandelbrotSet.eps \
	cartoons/UniprocessorUberAllesSmall.eps \
	cartoons/pipeline.eps \
	cartoons/ref.eps \
	cartoons/tollbooth.eps \
	cartoons/trackmeet.eps \
	cartoons/whippersnapper300.eps \
	cartoons/whippersnapper600.eps \
	count/GlobalInc.eps \
	count/GlobalTreeInc.eps \
	count/PerThreadInc.eps \
	count/count_lim.eps \
	count/sig-theft.eps \
	cpu/SystemArch.eps \
	datastruct/hashdiagram.eps \
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
	future/latencytrend.eps \
	future/be-lb-n4-rf-all.eps \
	future/be-lw-n4-rf-all.eps \
	intro/FourTaskCategories.eps \
	intro/FourTaskOrder.eps \
	intro/Generality.eps \
	intro/PPGrelation.eps \
	locking/DeadlockCycle.eps \
	locking/LayeredLockHierarchy.eps \
	locking/LocalLockHierarchy.eps \
	locking/NonLocalLockHierarchy.eps \
	locking/rnplock.eps

all: perfbook.pdf

perfbook.pdf: $(LATEXSOURCES) $(EPSSOURCES) extraction embedfonts
	sh utilities/runlatex.sh perfbook bib

perfbook-1c.pdf: $(LATEXSOURCES) $(EPSSOURCES) extraction embedfonts
	sed -e 's/,twocolumn//' -e '/^\\frontmatter/a \\\\pagestyle{plain}' -e 's/setboolean{twocolumn}{true}/setboolean{twocolumn}{false}/' < perfbook.tex > perfbook-1c.tex
	sh utilities/runlatex.sh perfbook-1c bib

perfbook_flat.tex: $(LATEXSOURCES) $(EPSSOURCES) embedfonts
	echo > qqz.tex
	texexpand perfbook.tex > perfbook_flat.tex
	sh utilities/extractqqz.sh < perfbook_flat.tex > qqz.tex

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

extraction: perfbook_flat.tex
	cat perfbook_flat.tex qqz.tex | sh utilities/extractcontrib.sh > contrib.tex
	sh utilities/extractorigpub.sh < perfbook_flat.tex > origpub.tex

embedfonts:
	sh utilities/fixfigfonts.sh
	sh utilities/fixdotfonts.sh
	sh utilities/eps2pdf.sh

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

count/sig-theft.eps: count/sig-theft.dot
	dot -Tps -o count/sig-theft.eps count/sig-theft.dot

clean:
	find . -name '*.aux' -o -name '*.blg' \
		-o -name '*.dvi' -o -name '*.log' \
		-o -name '*.qqz' -o -name '*.toc' | xargs rm
	rm -f perfbook_flat.tex perfbook_html.tex perfbook.out perfbook-1c.out
	rm -rf perfbook_html
	rm -f SMPdesign/DiningPhilosopher5.eps \
	      SMPdesign/DiningPhilosopher5TB.eps \
	      SMPdesign/DiningPhilosopher4part-b.eps \
	      SMPdesign/DiningPhilosopher5PEM.eps

distclean: clean
	sh utilities/cleanpdf.sh

neatfreak: distclean
	# Don't forget to regenerate the .pdf from each .svg file
	find . -name '*.pdf' | xargs rm
