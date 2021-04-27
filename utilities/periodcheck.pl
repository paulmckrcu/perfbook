#!/usr/bin/env perl
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Check LaTeX source of mid-sentence and end-of-sentence period
#
# Assumptions:
#    End-of-sentence periods are at the end of input lines.
#
# Exceptions:
#    LaTeX comments
#    LaTeX labels: such as \cref{fig:xxx:foo vs. bar}
#    Verbatim contents
#    Table contents
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
my $label_ptn = qr/(^|\{)(,?[a-z]{3}:[a-zMPS]+:[^\},]+)(\}|,)/ ;

sub check_line {
    my $line_raw = $line;
    if ($line =~ /$label_ptn/) {
	while ($line && $line =~ /$label_ptn/) {
	    my $quoted_2 = quotemeta $2;
	    $line =~ s/$quoted_2//;
	}
    }
    if ($line =~ /$Verbatim_begin/ ||
	$line =~ /$tabular_begin/) {
	$skip = 1;
    }
    unless ($skip) {
	$safe = 1;
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[A-Z]\.$/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[A-Z]\.\\footnote/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[Aa]cr\{.+\}\.$/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[Aa]crm\{.+\}\.$/) {
	    $safe = 0;
	    if ($next_line =~ /^\s*$/ || $next_line =~ /^\s*%/ ||
		$next_line =~ /\\item/ || $next_line =~ /\\end\{quot/ ||
		$next_line =~ /\\end\{enum/ || $next_line =~ /\\end\{item/) {
		$safe = 1;
	    }
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[a-z\}]\.\s[^\\]+/) {
	    $safe = 0;
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[^~]\\cite/) {
	    $safe = 0;
	    if ($line =~ /^(?=[\s]*+[^%])[^%]*~\(\\cite/) {
		$safe = 1;
	    }
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
