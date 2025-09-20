#!/usr/bin/env perl
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Check LaTeX source of percent sign
#
# Copyright (C) Akira Yokosawa, 2025
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

use strict;
use warnings;

my $line;
my $line_num = 0;
my $next_line;

sub check_percent {
    my $line_raw = $line;
    if ($line =~ /[0-9]+(\\,)?\\%/) {
	print $ARGV[0], ':', $line_num, ': ', $line_raw;
	print "Hint: Use \\pct for percent sign as unit, say \\pct\\ if no punct follows.\n";
    }
    if ($line =~ /[0-9]+\\pct[ \s]/) {
	print $ARGV[0], ':', $line_num, ': ', $line_raw;
	print "Hint: Say \\pct\\ in mid-sentence.\n";
    }
}

open(my $fh, '<:encoding(UTF-8)', $ARGV[0])
    or die "Could not open file '$ARGV[0]' $!";

$line = <$fh>;
$line_num = 1;
while($next_line = <$fh>) {
    check_percent();
    $line = $next_line;
    $line_num++ ;
}
check_percent();
