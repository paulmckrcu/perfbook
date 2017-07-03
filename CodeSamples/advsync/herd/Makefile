all: C-SB+o-o+o-o.litmus.out C-SB+o-mb-o+o-mb-o.litmus.out

%.litmus.out: %.litmus
	litmus7 -r 1000 -carch X86 $< > $@ 2>&1
