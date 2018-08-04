#!/bin/sh
./utilities/gen_snippet_d.pl > CodeSamples/snippets.d
rc=$?
if [ $rc != 0 ]
then
	rm -f CodeSamples/snippets.d
	exit 1
fi
