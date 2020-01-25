#!/usr/bin/perl
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Check LaTeX source of snippet extracted by fcvextract.pl
#
# Copyright (C) Akira Yokosawa, 2019
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

use strict;
use warnings;

my $line;
my $lnlbl_re;
my $checking = 0;
my $fcvlabel_re = qr/\\begin\{fcvlabel\}\[([^\]]*)\]/ ;
my $end_fcvlabel_re = qr/\\end\{fcvlabel\}/ ;
my $Verbatim_cmd_re = qr/\\begin\{Verbatim[LNU]\}\[commandchars=(.{6}).*\]/ ;
my $Verbatim_re = qr/\\begin\{Verbatim[LNU]\}/ ;
my $end_Verbatim_re = qr/\\end\{Verbatim[LNU]\}/ ;
my $commandchars = "";
my $esc_bsl;
my $esc_open;
my $esc_close;
my $esc_bsl_re;
my $esc_open_re;
my $esc_close_re;
my $line_count = 0;

my $fcv_file = $ARGV[0];
open(my $fh, '<:encoding(UTF-8)', $fcv_file)
    or die "Could not open file '$fcv_file' $!";

while($line = <$fh>) {
    $line_count = $line_count + 1;
    if ($line =~ /$fcvlabel_re/) {
	$checking = 1;
    }
    if ($checking == 3) {
	if ($line =~ /$end_fcvlabel_re/) {
	    $checking = 4;
	}
    }
    if ($checking == 2) {
	if ($line =~ /$end_Verbatim_re/) {
	    $checking = 3;
	} elsif ($commandchars =~ /\S/) {
	    $_ = $line;
	    s/$lnlbl_re//;
	    if (/$esc_bsl_re/ || /$esc_open_re/ || /$esc_close_re/) {
		die "commandchars collision detected in $fcv_file, line: $line_count\n$line\n";
	    }
	}
    }
    if ($checking == 1) {
	if ($line =~ /$Verbatim_cmd_re/) {
	    $commandchars = $1;
	    $esc_bsl = substr $commandchars, 0, 2;
	    $esc_open = substr $commandchars, 2, 2;
	    $esc_close = substr $commandchars, 4, 2;
	    $lnlbl_re = $esc_bsl."lnlbl".$esc_open.".*".$esc_close;
	    $esc_bsl_re = qr/$esc_bsl/;
	    $esc_open_re = qr/$esc_open/;
	    $esc_close_re = qr/$esc_close/;
	    $checking = 2;
	} elsif ($line =~ /$Verbatim_re/) {
	    $checking = 2;
	}
    }
    if (eof) {
	last;
    }
}
if ($checking == 4) {
    exit 0;
} else {
    die "incomplete fcv file $fcv_file\n";
}
