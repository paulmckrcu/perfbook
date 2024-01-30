#!/usr/bin/env perl
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Expand frequency data of the form:
#
#   1000 4
#   1004 2
#   1050 1
#
# into:
#
#   1000
#   1000
#   1000
#   1000
#   1004
#   1004
#   1050
#
# Copyright (C) Akira Yokosawa, 2024
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

use strict;
use warnings;

my $line;
my $freq;
my $count;

open(my $fn, '<:encoding(UTF-8)', $ARGV[0])
    or die "Could not open file '$ARGV[0]' $!";

while($line = <$fn>) {
    if ($line =~ /(\-?[0-9]+)\s+([0-9]+)/ ) {
	$freq = $1;
	$count = $2;
	for (my $i = 0; $i < $count; $i++) {
	    print "$freq\n";
	}
    }
}
