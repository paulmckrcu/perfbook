#!/usr/bin/env perl
#
# Move line of \QuickE{} below \end{enumerate} to just above
# the \end{enumerate}.
# Move line of \QuickE{} below \end{listing} to above
# \begin{listing} corresponding to it.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, you can access it online at
# http://www.gnu.org/licenses/gpl-2.0.html.
#
# Copyright (C) Akira Yokosawa, 2017
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

my $line;
my $after_end_enum = 0;
my $in_listing = 0;
my $after_listing = 0;
my $line_idx = 1;
my @line_buf;

$line_buf[1] = <>;
while($line = <>) {
    if ($after_end_enum) {
	if ($line =~ /\\QuickE\{\}/) {
	    print $line;
	} else {
	    print $line_buf[1];
	    $line_buf[1] = $line;
	}
	$after_end_enum = 0;
	next;
    }
    if ($in_listing) {
	if ($line =~ /\\end\{listing\}/) {
	    $after_listing = 1;
	    $in_listing = 0;
	}
	$line_buf[++$line_idx] = $line;
	next;
    }
    if ($after_listing) {
	if ($line =~ /%/) {
	    $line_buf[++$line_idx] = $line;
	    next;
	}
	if ($line =~ /\\QuickE\{\}/) {
	    print $line;
	    for my $i (1 .. $line_idx-1) {
		print $line_buf[$i];
	    }
	    $line_buf[1] = $line_buf[$line_idx];
	} else {
	    for my $i (1 .. $line_idx) {
		print $line_buf[$i];
	    }
	    $line_buf[1] = $line;
	}
	$line_idx = 1;
	$after_listing = 0;
	next;
    }
    if ($line =~ /\\end\{enumerate\}/) {
	print $line_buf[1];
	$line_buf[1] = $line;
	$after_end_enum = 1;
	next;
    }
    if ($line =~ /\\begin\{listing\}/) {
	$in_listing = 1;
	$line_buf[++$line_idx] = $line;
	next;
    }
    print $line_buf[1];
    $line_buf[1] = $line;
}
print $line_buf[1];
