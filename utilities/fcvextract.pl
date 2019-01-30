#!/usr/bin/perl
# SPDX-License-Identifier: GPL-2.0-or-later
#
# Extract "VerbatimL" source from code sample with labels to lines
#
# Usage:
#
# $ utilities/fcvextract.pl <code sample file> <snippet identifier>
#
# Example:
#
# $ utilities/fcvextract.pl CodeSamples/api-pthreads/api-pthreads.h \
#        api-pthreads:waitall
#
# Example of a snippet in <code sample file>:
#
# ---
# /*
#  * Wait on all child processes.
#  */
# static __inline__ void waitall(void)
# {
# // \begin{snippet}[labelbase=ln:toolsoftrade:api-pthreads:waitall,commandchars=\%\[\]]
# 	int pid;
# 	int status;
#
# 	for (;;) {				//\lnlbl{loopa}
# 		pid = wait(&status);		//\lnlbl{wait}
# 		if (pid == -1) {
# 			if (errno == ECHILD)	//\lnlbl{ECHILD}
# 				break;		//\lnlbl{break}
# 			perror("wait");		//\lnlbl{perror}
# 			exit(EXIT_FAILURE);	//\lnlbl{exit}
# 		}
# 		poll(NULL, 0, 1);		//\fcvexclude
# 	}					//\lnlbl{loopb}
# // \end{snippet}
# }
# ---
#
# VerbatimL source extracted from above (VerbatimL is a customized
# Verbatim environment of fancyvrb package):
#
# ---
# \begin{linelabel}[ln:toolsoftrade:api-pthreads:waitall]
# \begin{VerbatimL}[commandchars=\%\[\]]
# 	int pid;
# 	int status;
#
# 	for (;;) {%lnlbl[loopa]
# 		pid = wait(&status);%lnlbl[wait]
# 		if (pid == -1) {
# 			if (errno == ECHILD)%lnlbl[ECHILD]
# 				break;%lnlbl[break]
# 			perror("wait");%lnlbl[perror]
# 			exit(EXIT_FAILURE);%lnlbl[exit]
# 		}
# 	}%lnlbl[loopb]
# \end{VerbatimL}
# \end{linelabel}
# ---
#
# <snippet identifier> corresponds to a meta command embedded in
# a code sample.
#
# 2nd argument to this script can match the tail part of labelbase string.
# In the above example, any of "waitall", "api-pthreads:waitall", or
# "toolsoftrace:api-pthreads:waitall" match the <snippet identifier>
#
# The meta command can have a "commandchars" option to specify an escape-
# character set for the escape-to-LaTeX feature. The option looks like:
#
# // \begin{snippet}[...,commandchars=\%\[\]]
#
# This directs "%" -> "\", "[" -> "{", and "[" -> "}" conversions to
# be done in the "VerbatimL" environment.
# In a code sample, a label to a particular line of code can be put
# as a meta command \lnlbl{} in comment as shown above.
# This script converts the \lnlbl{} commands with these charcters
# reverse-converted.
#
# To make the actual labels to have the full form of
#
#     "ln:<chapter>:<file name>:<function>:<line label>"
#
# in LaTeX processing, this script will enclose the snippet with
# a pair of \begin{linelabel} and \end{linelabel} as shown above.
#
# To omit a line in extracted snippet, put "\fcvexclude" in comment
# on the line.
#
# By default, comment blocks of the form "/* ... */" in C language
# code will be removed in the extracted snippet. To keep those blocks,
# put an option "keepcomment=yes" to \begin{snippet} meta command.
#
# Also, this script recognizes #ifndef -- #else -- #endif conditional
# of the following form to allow alternative code for snippet:
#
#	#ifndef FCV_SNIPPET
#		<actual code>
#	#else
#		<alternative code for snippet>
#	#endif
#
# NOTE: "#ifdef FCV_SNIPPET" is not recognized.
#	"#else" can be omitted.
#
# Copyright (C) Akira Yokosawa, 2018, 2019
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

use strict;
use warnings;

my $src_file;
my $c_src = 0;
my $lnlbl_re;
my $lnlbl_re2;
my $line;
my $edit_line;
my $extract_labelbase;
my $begin_re;
my $end_re;
my $extracting = 0;
my $esc_char;
my $esc_bsl;
my $esc_open;
my $esc_close;
my $dir_name;
my $file_name;
my $func_name;
my $label;
my $env_name = "VerbatimL" ;
my $keepcomment = 0;
my $incomment = 0;
my $ifndef = 0;
my $other_opts;

$src_file = $ARGV[0];
$extract_labelbase = $ARGV[1];

$begin_re = qr/\\begin\{snippet\}.*labelbase=[^,\]]*$extract_labelbase[,\]]/ ;
$end_re = qr/\\end\{snippet\}/;

if ($src_file =~ /.*\.[ch]$/ || $src_file =~ /.*\.spin$/) {
    $lnlbl_re = qr!(.*?)(\s*//\s*)\\lnlbl\{(.*)}\s*$!;
    $lnlbl_re2 = qr!(.*?)(s*/\*\s*)\\lnlbl\{(.*)}\s*\*/(.*)$!;
    $c_src = 1;
} elsif ($src_file =~ /.*\.sh$/ ) {
    $lnlbl_re = qr!(.*?)(\s*#\s*)\\lnlbl\{(.*)}\s*$!;
} elsif ($src_file =~ /.\.ltms$/ ) {
    $lnlbl_re = qr!(.*?)(\s*//\s*)\\lnlbl\{(.*)}\s*$!;
} else {
    die ("unkown file suffix!");
}

while($line = <>) {
    if ($line =~ /$begin_re/) {
	$extracting = 1;
    }
    if (eof) {
	last;
    }
    if ($extracting == 2) {
	if ($line =~ /$end_re/) {
	    last;
	}
	if ($line =~ /\\fcvexclude/) {
	    next; # skip this line
	}
	if ($c_src && $line =~ m!$lnlbl_re2!) {
	    $line = $1 . $esc_bsl . "lnlbl" . $esc_open . $3 . $esc_close . $4 . "\n" ;
	}
	if ($c_src && !$keepcomment) {
	    if ($incomment) {
		if ($line =~ /\*\/(.*$)/) {
		    $line = $1;
		    $incomment = 0;
		} else {
		    $line = "";
		}
	    } else {
		if ($line =~ /(.*)\/\*.*\*\/(.*)/) {
		    $line = $1 . $2;
		    if ($line =~ /\S/) {
			$line = $line . "\n";
		    } else {
			next;
		    }
		} elsif ($line =~ /(.*)\/\*.*/) {
		    $line = $1;
		    $incomment = 1;
		}
	    }
	}
	if ($ifndef == 1) {
	    if ($line =~ /\#else/) {
		$ifndef = 2;
	    } elsif ($line =~ /\#endif/) {
		$ifndef = 0;
	    }
	    next;
	}
	if ($ifndef == 2) {
	    if ($line =~ /\#endif/ ) {
		$ifndef = 0;
		next;
	    }
	}
	if ($c_src && $line =~ /\#ifndef\s+FCV_SNIPPET/) {
	    $ifndef = 1;
	    next;
	}
	if ($line =~ m!$lnlbl_re!) {
	    $edit_line = $1 . $esc_bsl . "lnlbl" . $esc_open . $3 . $esc_close ;
	    print $edit_line . "\n" ;
	} elsif ($line eq "") {
	    next;
	} else {
	    print $line ;
        }
    }
    if ($extracting == 1) {
	print "% Do not edit!\n" ;
	print "% Generated by utilities/fcvextract.pl.\n" ;
	if ($line =~ /labelbase=([^,\]]+)/) {
	    print "\\begin\{linelabel}\[$1\]\n" ;
	    $_ = $line ;
	    s/labelbase=[^,\]]+,?// ;
	    $line = $_ ;
	}
	if ($line =~ /style=N[,\]]/) {
	    $env_name = "VerbatimN" ;
	    $_ = $line ;
	    s/style=N,?// ;
	    $line = $_ ;
	} elsif ($line =~ /style=U[,\]]/) {
	    $env_name = "VerbatimU" ;
	    $_ = $line ;
	    s/style=U,?// ;
	    $line = $_ ;
	}
	print "\\begin\{$env_name\}" ;

	if ($line =~ /commandchars=([^,]+).*\]/) {
	    $esc_char = $1 ;
	    print "\[commandchars=" . $esc_char ;
	    $esc_bsl = substr $esc_char, 1, 1;
	    $esc_open = substr $esc_char, 3, 1;
	    $esc_close = substr $esc_char, 5, 1;
	    $_ = $line ;
	    s/commandchars=.{6},?// ;
	    $line = $_ ;
	} else {
	    $esc_bsl = "\\" ;
	    $esc_open = "\{" ;
	    $esc_close = "\}" ;
	}
	if ($line =~ /keepcomment=([^,\]]+).\]/) {
	    if ($1 eq "yes") {
		$keepcomment = 1;
	    }
	    $_ = $line;
	    s/keepcomment=[^,\]]+,?// ;
	    $line = $_ ;
	}
	if ($line =~ /\[(.*)\]$/) {
	    $_ = $1 ;
	    s/,$// ;
	    $other_opts = $_ ;
	}
	if ($other_opts ne '') {
	    print ",$other_opts\]\n";
	} else {
	    print "\]\n";
	}
	$extracting = 2;
    }
}
if ($extracting == 2) {
    print "\\end\{$env_name\}\n\\end\{linelabel\}\n" ;
    exit 0;
} else {
    exit 1;
}
