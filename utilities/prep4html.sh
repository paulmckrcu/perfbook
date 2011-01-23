#!/bin/sh
#
# Create a perfbook_html.tex on standard output from a perfbook_flat.tex
# on standard input that converts the special-purpose perfbook-only
# commands into something that latex2html can understand.
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
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
#
# Copyright (C) IBM Corporation, 2011
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

gawk '
/^\\renewcommand\\/ {
	print "%%prep4html.sh%%" $0
	printed = 1;
}

/\\textcopyright/ {
	print "%%prep4html.sh%%" $0
	gsub(/\\textcopyright/, "(c)");
	print "%%prep4html.sh%%" $0
}

/^\\QuickQuizChapter{/ {
	print "%%prep4html.sh%%" $0
	l = $0;
	quickquizctr = 0;
	split(l,a,/{/);
	curchplabel = a[2];
	sub(/}/,"",curchplabel);
	curchpname = a[3];
	sub(/}/,"",curchpname);
	print "\\chapter{" curchpname "}"
	print "\\label{" curchplabel "}"
	print "%%prep4html.sh%% " $0
	printed = 1;
}

/^\\QuickQuiz{/ {
	quickquizctr++;
	print "%%prep4html.sh%% " $0
	print "\\textbf{Quick Quiz \\thechapter" quickquizctr ":}"
	print "%%prep4html.sh%% " $0
	printed = 1;
}

/^\\QuickQuizAnswer{/ {
	print "%%prep4html.sh%% " $0
	print "\\textbf{End Quick Quiz}"
	/* Let it print the original to eat the answer. */
	noprint = 1;
}

/^} \\QuickQuizEnd/ {
	printed = 1;
	noprint = 0;
}

/^\\QuickQuizAnswers/ {
	print "%%prep4html.sh%% " $0
	print "\\chapter{Answers to Quick Quizzes}"
	print "\\label{chp:Answers to Quick Quizzes}"
	print "~ \\\\"
	print "\\input{qqz_html}"
	print "%%prep4html.sh%% " $0
	printed = 1;
}

/^\\QuickQAC{/ {
	print "%%prep4html.sh%% " $0
	l = $0;
	quickquizctr = 0;
	split(l,a,/{/);
	curchplabel = a[2];
	sub(/}/,"",curchplabel);
	curchpref = "\\ref{" curchplabel "}"
	curchpname = a[3];
	sub(/}/,"",curchpname);
	print "\\section{Chapter~" curchpref "}"
	print "%%prep4html.sh%% " $0
	printed = 1;
}

/^\\QuickQ{/ {
	quickquizctr++;
	print "%%prep4html.sh%% " $0
	print "\\textbf{Quick Quiz " curchpref "." quickquizctr ":} ~ \\\\ "
	print "%%prep4html.sh%% " $0
	printed = 1;
}

/^\\QuickA{/ {
	print "%%prep4html.sh%% " $0
	print "\\\\ ~ \\\\ \\textbf{Answer:} \\\\"
	print "%%prep4html.sh%% " $0
	printed = 1;
}

{
	if (printed || noprint)
		printed = 0;
	else
		print;
}'

