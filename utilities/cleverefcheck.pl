#!/usr/bin/perl
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Check LaTeX source of cleveref macros usages
#
# Assumptions:
#    End-of-sentence fullstops are at the end of input lines.
#
# Copyright (C) Akira Yokosawa, 2021
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

use strict;
use warnings;

my $line;
my $new_sentence = 1;
my $line_num = 0;
my $skip = 0;
my $ng = 0;
my $Verbatim_begin = qr/\\begin\{(Verbatim|tabula|equation|SaveVerb|verbbox)/ ;
my $Verbatim_end = qr/\\end\{(Verbatim|tabula|equation|SaveVerb|verbbox)/ ;
my $label_ptn = qr/(^\s*|\{)(,?[a-z]{3,4}:([a-zMPS]+:)?[^\},]+)(\}|,)/ ;
my $IX_ptn = qr/(^|\s+)IX[^\s\{]*{/ ;
my $api_ptn = qr/(^|\s+)api[^\s\{]*{/ ;
my $ppl_ptn = qr/(^|\s+)ppl[^\s\{]*{/ ;
my $acr_ptn = qr/(^|\s+)[aA]cr[^\s\{]*{/ ;
my $in_footnote = 0 ;
my $footnote_save = 0;

sub check_line {
    my $raw_line = $line;
    $line =~ s/\\%/pct/g ;
    if ($line =~ /$Verbatim_begin/) {
	$skip = 1;
    }
    if ($line =~ /$label_ptn/) {# remove label string
	while ($line && $line =~ /$label_ptn/) {
	    my $quoted_2 = quotemeta $2;
	    $line =~ s/$quoted_2//;
	}
    }
    if ($line =~ /\\[tq]?co\{([^\}]+)\}/) {# remove \co{} argument
	while ($line && $line =~ /((\\[tq]?co\{)[^\}]+)\}/) {
	    my $quoted_1 = quotemeta $1;
	    my $quoted_2 = quotemeta $2;
	    $line =~ s/$quoted_1/$quoted_2/;
	}
    }
    unless ($skip) {
	$ng = 0;
	if ($line =~ /^(?=[\s]*+[^%])[^%]*\\ref\{/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*\\pageref\{/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*\\lnref\{/) {
	    $ng += 1;
	    if ($line =~ /or~\\lnref\{/ ||
		$line =~ /item~\\ref\{/) {
		$ng -= 1;
	    }
	}
	if ($new_sentence != 0 &&
	    ($line =~ /^\s*\\cref/ || $line =~ /^\s*\\cpageref/ ||
	     $line =~ /^\s*\\clnref/)) {
	    $ng += 1;
	}
	if ($new_sentence == 0 &&
	    ($line =~ /^\s*\\Cref/ || $line =~ /^\s*\\Cpageref/ ||
	     $line =~ /^\s*\\Clnref/)) {
	    $ng += 1;
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*[^\s]+\s*\\Cref/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[^\s]+\s*\\Cpageref/ ||
	    $line =~ /^(?=[\s]*+[^%])[^%]*[^\s]+\s*\\Clnref/) {
	    $ng += 1;
	    if ($line =~ /^(?=[\s]*+[^%])[^%]*^\s*\\item\s+\\C/ ) {
		$ng -= 1;
	    }
	}
	if ($line =~ /^(?=[\s]*+[^%])[^%]*^\s*\\item\s+[a-z]/ ) {
	    $ng += 1;
	}
	if ($new_sentence) {
	    if ($line =~ /^\s*`*[a-z]/ || $line =~ /^\s*\\acr/ ||
		$line =~ /^\s*\\IX[^A\{]*\{[a-z]/ ) {
		$ng += 1;
	    }
	}
	if ($new_sentence == 2) { # after colon
	    if ($line =~ /^\s*\([0-9a-z]+\)/ ) {
		$ng += 1;
	    }
	}
	if ($line =~ /^[ ]{8}/ ||  # indent by white speces (should be TAB)
	    $line =~ /^(?=[\s]*+[^%])[^%][ ]+\t/) { # TAB after white space
	    $ng += 1;
	}
	if ($line =~ /$IX_ptn/ || $line =~ /$api_ptn/ ||
	    $line =~ /$ppl_ptn/ || $line =~ /$acr_ptn/ ) {
	    $ng += 1;
	}
	if ($ng) {
	    print $ARGV[0], ':', $line_num, ':', $raw_line;
	}
    }
    if ($line =~ /$Verbatim_end/) {
	$skip = 0;
    } else {
	unless ($line =~ /\\begin\{fcvref\}/ || $line =~ /\\end\{fcvref\}/ ||
		$line =~ /^\s*\}\s*$/ || $line =~ /^\s*%/) {
	    if ($line =~ /^(?=[\s]*+[^%])[^%]*[\.\?!]\s*[\)\}\']*\s*(%.*)?$/ ||
		$line =~ /^\s*$/ || $line =~ /\\begin\{quote\}/ ||
		$line =~ /^\\E?QuickQuiz[BEM]?\{/ ||
		$line =~ /\\E?QuickQuizAnswer[BEM]?\{/ ) {
		$new_sentence = 1;
	    } else {
		$new_sentence = 0;
		if ($line =~ /^(?=[\s]*+[^%])[^%]*:\s*[\)\}\']*\s*(%.*)?$/ ) {
		    $new_sentence = 2;  # colon
		}
	    }
	}
	if ($in_footnote) {
	    if ($line =~ /[\.\?!\']\}\s*$/ ) {
		$in_footnote = 0 ;
		$new_sentence = $footnote_save ;
	    }
	}
	if ($line =~ /\\footnote\{\s*$/ ) {
	    $in_footnote = 1;
	    $new_sentence = 1;
	    if ($line =~ /\.\\footnote\{\s*$/ ) {
		$footnote_save = 1 ;
	    } else {
		$footnote_save = 0 ;
	    }
	}
    }
}

open(my $fh, '<:encoding(UTF-8)', $ARGV[0])
    or die "Could not open file '$ARGV[0]' $!";

while($line = <$fh>) {
    $line_num++ ;
    check_line();
}
