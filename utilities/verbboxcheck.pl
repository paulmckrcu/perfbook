#!/usr/bin/perl
#
# Check usage pattern of "verbbox" environment
#
# This script searches \begin{figure} within a few lines ahead of
# \theverbbox.
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
# Copyright (C) Akira Yokosawa, 2016
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

my $line;
my $in_figure = 0;
my $interval = 0;
my $line_num = 1;
my $fig_line;
my $fig_line_num;
my $infile = $ARGV[0];

while($line = <>) {
    if ($in_figure) {
	if ($line =~ /\\theverbbox/) {
	    print "$infile:$fig_line_num:$fig_line";
	    $in_figure = 0;
	}
	$interval++;
    }
    if ($line =~ /\\begin\{figure\}/) {
	$in_figure = 1;
	$fig_line = $line;
	$fig_line_num = $line_num;
    }
    if ($interval > 3) {
	$in_figure = 0;
	$interval = 0;
    }
    $line_num++;
}
