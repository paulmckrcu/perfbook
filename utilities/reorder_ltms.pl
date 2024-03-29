#!/usr/bin/env perl
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Reorder meta command lines in .litmus source to work around
# restrictions of herdtools7 where comments can be placed.
#
# .litmus files need to have "C foo-bar" at the very beginning.
# They need to have an "exists" clause as the final line.
#
# Also, "{" and "}" in comments sometimes cause error depending
# on their position. So we use "[" and "]" in .litmus files.
#
# Example:
# Input
# ------------------------------------------------------------
# C C-foo-bar
# //\begin[snippet][labelbase=ln:foo-bar,commandchars=\%\[\]]
# [...]
#     r1 = READ_ONCE(*x0);    //\lnlbl[read]
# [...]
# //\end[snippet]
# exists (0:r1=0 /\ 1:r1=0)
# ------------------------------------------------------------
# Output
# ------------------------------------------------------------
# //\begin{snippet}[labelbase=ln:foo-bar,commandchars=\%\[\]]
# C C-foo
# [...]
#     r1 = READ_ONCE(*x0);    //\lnlbl{read}
# [...]
# exists (0:r1=0 /\ 1:r1=0)
# //\end{snippet}
# ------------------------------------------------------------
#
# Copyright (C) Akira Yokosawa, 2018
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

use strict;
use warnings;

my $src_file = $ARGV[0];
my $line;
my $edit_line;
my $first_line;
my $end_command;
my $lnlbl_command;
my $status = 0;	# 0: just started, 1: first_line read; 2: begin line output,
		# 3: final line

while($line = <>) {
    if (eof) {
	if ($line =~ /\\lnlbl\[[^\]]*\]/) {
	    $_ = $line ;
	    s/\\lnlbl\[([^\]]*)\]/\\lnlbl\{$1\}/ ;
	    $line = $_ ;
	}
	if ($line =~ /\(\*\s*\\lnlbl\{[^\}]*\}\s*\*\)/) {
	    $_ = $line ;
	    s/\(\*\s*(\\lnlbl\{[^\}]*\})\s*\*\)/\/\/$1/ ;
	    $line = $_ ;
	}
	print $line ;
	$status = 3;
	last;
    }
    if ($status == 0) {
	$first_line = $line;
	$status = 1;
	print "// Do not edit!\n// Generated by utillities/reorder_ltms.pl\n";
	next;
    } elsif ($status == 1) {
	$_ = $line;
	s/\\begin\[snippet\]/\\begin\{snippet\}/;
	$edit_line = $_ ;
	print $edit_line ;
	print $first_line ;
	$status = 2;
	next;
    } elsif ($status == 2) {
	if ($line =~ /\\end\[snippet\]/) {
	    $_ = $line ;
	    s/\\end\[snippet\]/\\end\{snippet\}/ ;
	    $end_command = $_ ;
	    next;
	} else {
	    if ($line =~ /\\lnlbl\[[^\]]*\]/) {
		$_ = $line ;
		s/\\lnlbl\[([^\]]*)\]/\\lnlbl\{$1\}/ ;
		$line = $_ ;
	    }
	    if ($line =~ /\(\*\s*\\lnlbl\{[^\}]*\}\s*\*\)/) {
		$_ = $line ;
		s/\(\*\s*(\\lnlbl\{[^\}]*\})\s*\*\)/\/\/$1/ ;
		$line = $_ ;
	    }
	    print $line ;
	}
    }
}

if ($status == 3) {
    print $end_command;
} else {
    die ("Oops, something went wrong!");
}
