#!/bin/sh

: ${GREP:=grep}
CREFPTN='\\[Cc](ln)?ref[{][^}]+}\s*[{][^}]+}'

tex_sources_all=`find . -name "*.tex" -print`
tex_sources=""

for f in $tex_sources_all
do
	case $f in
	./perfbook*) ;;
	./qqz*) ;;
	./glsdict.tex) ;;
	./origpub.tex) ;;
	./contrib.tex) ;;
	./future/HTMtable*) ;;
	./SMPdesign/DiningPhilosopher*) ;;
	./appendix/styleguide*) ;;
	*) tex_sources="$tex_sources $f" ;;
        esac
done

for g in $tex_sources
do
	utilities/cleverefcheck.pl $g
	if $GREP -q -zo -E $CREFPTN $g ; then
		echo "------" ;
		if $GREP -q -E $CREFPTN $g ; then
			$GREP -n -B 2 -A 2 -E $CREFPTN $g
		else
			$GREP -zo -B 2 -A 2 -E $CREFPTN $g
			echo
		fi
		echo "------"
		echo "Need to use \[Cc]refrange or \[Cc]lnrefrange in $g."
	fi
done
