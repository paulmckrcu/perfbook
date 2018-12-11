#!/bin/sh

awk < perfbook_flat.tex '
BEGIN {
	title = "???"
	prefix = "???"
}

/^\\QuickQuizChapter{/ || /^\\chapter/ {
	title = $0;
	prefix = "";
}

/^\\section{/ {
	title = $0;
	prefix = "\t";
}

/^\\[Ee]pigraph{/ {
	print prefix title;
	print prefix "%";
	in_epigraph = 1;
}

/^$/ && in_epigraph {
	in_epigraph = 0;
	prefix = "???";
	title = "???";
	print $0;
}

in_epigraph {
	print prefix $0 "";
}'
