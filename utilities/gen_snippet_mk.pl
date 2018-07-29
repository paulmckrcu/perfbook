#!/usr/bin/perl

use strict;
use warnings;

my @fcvsources;
my $snippet_key;
my $source;
my $src_under_sub;
my @snippet_commands;
my $snippet;
my $fname;
my $subdir;

$snippet_key = '\\begin\{snippet\}' ;
@fcvsources = `grep -l -r -F $snippet_key CodeSamples` ;
chomp @fcvsources ;

print "FCVSNIPPETS = " ;
foreach $source (@fcvsources) {
    @snippet_commands = `grep -F $snippet_key $source` ;
    chomp @snippet_commands ;
    $source =~ m!.*/([^/]+)/[^/]+! ;
    $subdir = $1 ;
    foreach $snippet (@snippet_commands) {
	$snippet =~ /labelbase=.*:(.+:[^,\]]+)[,\]]/ ;
	$_ = $1;
	s/:/@/g ;
	print "\\\n\t$subdir/$_.fcv ";
    }
}

print "\n\n\.PHONY: all clean\n\n" ;
print "all: \$\(FCVSNIPPETS\)\n\n" ;

foreach $source (@fcvsources) {
    @snippet_commands = `grep -F $snippet_key $source` ;
    chomp @snippet_commands ;
    $src_under_sub = $source ;
    $source =~ m!.*/([^/]+)/[^/]+! ;
    $subdir = $1 ;
    $src_under_sub =~ s/CodeSamples\/// ;
#    print @snippet_commands ;
    foreach $snippet (@snippet_commands) {
	$snippet =~ /labelbase=.*:(.+:[^,\]]+)[,\]]/ ;
	$_ = $1;
	s/:/@/g ;
	print "$subdir/$_.fcv: $src_under_sub\n";
    }
}

print "\n\$\(FCVSNIPPETS\):\n" ;
print "\t\@echo \"\$< --> \$\@\"\n" ;
print "\t\@../utilities/fcvextract.pl \$< \$\(subst \@,:,\$\(basename \$\(notdir \$\@\)\)\) > \$\@\n" ;
print "\nclean:\n\trm -f \$\(FCVSNIPPETS\)\n" ;
