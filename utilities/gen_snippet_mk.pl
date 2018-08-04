#!/usr/bin/perl

use strict;
use warnings;

my @fcvsources;
my $snippet_key;
my $source;
my $src_under_sub;

$snippet_key = '\\begin\{snippet\}' ;
@fcvsources = `grep -l -r -F $snippet_key CodeSamples` ;
chomp @fcvsources ;

print "FCVSNIPPETS = " ;
foreach $source (@fcvsources) {
    my @snippet_commands1 ;
    my $subdir ;
    my $snippet ;
    @snippet_commands1 = `grep -F $snippet_key $source` ;
    chomp @snippet_commands1 ;
    $source =~ m!.*/([^/]+)/[^/]+! ;
    $subdir = $1 ;
    foreach $snippet (@snippet_commands1) {
	$snippet =~ /labelbase=.*:(.+:[^,\]]+)[,\]]/ ;
	$_ = $1;
	s/:/@/g ;
	print "\\\n\t$subdir/$_.fcv ";
    }
}

print "\n\n\.PHONY: all clean\n\n" ;
print "all: \$\(FCVSNIPPETS\)\n\n" ;

foreach $source (@fcvsources) {
    my @snippet_commands2 ;
    my $src_under_sub ;
    my $subdir ;
    my $snippet ;
    @snippet_commands2 = `grep -F $snippet_key $source` ;
    chomp @snippet_commands2 ;
    $src_under_sub = $source ;
    $source =~ m!.*/([^/]+)/[^/]+! ;
    $subdir = $1 ;
    $src_under_sub =~ s/CodeSamples\/// ;
#    print @snippet_commands ;
    foreach $snippet (@snippet_commands2) {
	$snippet =~ /labelbase=.*:(.+:[^,\]]+)[,\]]/ ;
	if (not defined $1) {
	    die("Oops! Please try \"make clean; make\".\n") ;
	}
	$_ = $1;
	s/:/@/g ;
	print "$subdir/$_.fcv: $src_under_sub\n";
    }
}

print "\n\$\(FCVSNIPPETS\):\n" ;
print "\t\@echo \"\$< --> \$\@\"\n" ;
print "\t\@../utilities/fcvextract.pl \$< \$\(subst \@,:,\$\(basename \$\(notdir \$\@\)\)\) > \$\@\n" ;
print "\nclean:\n\trm -f \$\(FCVSNIPPETS\)\n" ;
