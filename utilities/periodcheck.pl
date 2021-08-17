#!/usr/bin/env perl
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Check LaTeX source of mid-sentence and end-of-sentence
# punctuations
#
# Assumptions:
#    End-of-sentence punctuations are at the end of input lines.
#
# Exceptions:
#    LaTeX comments
#    LaTeX labels: such as \cref{fig:xxx:foo vs. bar}
#    Verbatim contents
#    Table contents
#    Middle-of-sentence punctuations properly annotated at the
#	end of input lines
#
# Copyright (C) Akira Yokosawa, 2021
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

use strict;
use warnings;

my $line;
my $next_line;
my $line_num = 0;
my $skip = 0;
my $ng;
my $Verbatim_begin = qr/\\begin\{(Verbatim|tabula|equation)/ ;
my $Verbatim_end = qr/\\end\{(Verbatim|tabular|equation)/ ;
my $label_ptn = qr/(^\s*|\{)(,?[a-z]{3,4}:([a-zMPS]+:)?[^\},]+)(\}|,)/ ;

sub check_line {
    my $line_raw = $line;
    $line =~ s/\\%/pct/g ;	# replace \% to prevent false negative
    if ($line =~ /$label_ptn/) {# remove label string
	while ($line && $line =~ /$label_ptn/) {
	    my $quoted_2 = quotemeta $2;
	    $line =~ s/$quoted_2//;
	}
    }
    if ($line =~ /\\[tq]?co\{([^\}]*)\}/ ) {
	while ($line && $line =~ /((\\[tq]?co\{)[^\}]+)\}/) {
	    my $quoted_1 = quotemeta $1;
	    my $quoted_2 = quotemeta $2;
	    $line =~ s/$quoted_1/$quoted_2/;
	}
    }
    # \QuickQuizChapter and \OriginalPublished don't allow line breaks in their
    # arguments.
    if ($line =~ /\\QuickQuizChapter\{/ ) {
	$line = '\\QuickQuizChapter\{\}\{\}\{\}';
    }
    if ($line =~ /\\OriginallyPublished\{/ ) {
	$line = '\\OriginallyPublised\{\}\{\}\{\}\{\}';
    }
    if ($line =~ /$Verbatim_begin/ ) {  # exception (verbatim ,tabular, equation)
	$skip = 1;
    }
    unless ($skip) {
	$ng = 0;
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[A-Z][\)\']*[\.\?\!\:][\)\}\']*$/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[A-Z][\)\']*[\.\?\!\:]\\footnote/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[Aa]crm?(f|fst)?\{.+\}[\)\']*[\.\?\!\:][\)\}\']*$/ ) {
	    $ng += 1;
	    if ($next_line =~ /^\s*$/ || $next_line =~ /^\s*%/ ||
		$next_line =~ /\\item/ ||
		$next_line =~ /\\E?QuickQuizAnswer[BEM]?\{/ ||
		$next_line =~ /\\E?QuickQuizEnd[BEM]?/ ||
		$next_line =~ /\\end\{(quot|enum|item|sequ)/ ) {
		$ng -= 1;
	    }
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[a-z][\)\}\']*[\.\?\!][\)\}\']*\s+[^%]/ ||
#	    $line =~ /^(?=[\s]*+[^%])[^%]*.*\.[\)\}\']*\s+[^%]/ ||  # Uncomment for full check
	    $line =~ /^(?=[\s]*+[^%])[^%]*.*:[\)\}\']*\s+[^%]/ ) {
	    $ng += 1;
	    if ($line =~ /^(?=[\s]*+[^%])[^%]*[a-z][\)\}\']*[\.\?\!][\)\}\']*\s+\\\\/ ||
		$line =~ /^(?=[\s]*+[^%])[^%]*.*[\.:][\)\}\']*\s+\\\\/ ) {
		$ng -= 1;
	    }
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[^~]\\cite/) {
	    $ng += 1;
	    if ($line =~ /^(?=[\s]*+[^%])[^%]*~\(\\cite/) {
		$ng -= 1;
	    }
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*\\\@[\.\?\!\:][\)\}\']*\s+[^%]/){
	    $ng += 1;
	}
	if ($ng) {
	    print $ARGV[0], ':', $line_num, ':', $line_raw;
	}
    }
    if ($line =~ /$Verbatim_end/ ) {
	$skip = 0;
    }
}

open(my $fh, '<:encoding(UTF-8)', $ARGV[0])
    or die "Could not open file '$ARGV[0]' $!";

$line = <$fh>;
$line_num = 1;
while($next_line = <$fh>) {
    check_line();
    $line = $next_line;
    $line_num++ ;
}
check_line();
