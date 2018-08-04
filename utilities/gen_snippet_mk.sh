#!/bin/sh
./utilities/gen_snippet_mk.pl > CodeSamples/snippets.mk
rc=$?
if [ $rc != 0 ]
then
	rm -f CodeSamples/snippets.mk
	exit 1
fi
