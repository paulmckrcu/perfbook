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
my $safe = 0;
my $Verbatim_begin = qr/\\begin\{Verbatim/ ;
my $Verbatim_end = qr/\\end\{Verbatim/ ;
my $tabular_begin = qr/\\begin\{tabula/ ;
my $tabular_end = qr/\\end\{tabula/ ;
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
    if ($line =~ /section\{([^\}]*)\}/ ) {
	my $quoted_1 = quotemeta $1;
	$line =~ s/$quoted_1//;
    }
    if ($line =~ /caption\{([^\}]*)\}/ ) {
	my $quoted_1 = quotemeta $1;
	$line =~ s/$quoted_1//;
    }
    if ($line =~ /$Verbatim_begin/ ||
	$line =~ /$tabular_begin/) {  # exception (verbatim and tabular)
	$skip = 1;
    }
    unless ($skip) {
	$safe = 1;
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[A-Z][\.\?\!][\)\}\']*$/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[A-Z][\.\?\!]\\footnote/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[Aa]crm?\{.+\}[\.\?\!][\)\}\']*$/ ) {
	    $safe = 0;
	    if ($next_line =~ /^\s*$/ || $next_line =~ /^\s*%/ ||
		$next_line =~ /\\item/ ||
		$next_line =~ /\\E?QuickQuizAnswer[BEM]?\{/ ||
		$next_line =~ /\\E?QuickQuizEnd[BEM]?/ ||
		$next_line =~ /\\end\{(quot|enum|item|sequ)/ ) {
		$safe = 1;
	    }
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[a-z\}][\.\?\!][\)\}\']*\s[^\\]+/) {
	    $safe = 0;
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[^~]\\cite/) {
	    $safe = 0;
	    if ($line =~ /^(?=[\s]*+[^%])[^%]*~\(\\cite/) {
		$safe = 1;
	    }
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*\\\@[\.\?\!][\)\}\']*\s+[^\s%]+/){
	    $safe = 0;
	}
	unless ($safe) {
	    print $ARGV[0], ':', $line_num, ':', $line_raw;
	}
    }
    if ($line =~ /$Verbatim_end/ ||
	$line =~ /$tabular_end/) {
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
