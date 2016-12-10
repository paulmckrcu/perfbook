#!/bin/sh
# Check the presence of "mpost" in LaTeX sources
#
# A POC of an arbitrary code execution vulnerability in the default
# configuration of TeX packages was disclosed at
# https://scumjr.github.io/2016/11/28/pwning-coworkers-thanks-to-latex/.
# TeX Live 2016 is updated on November 30, 2016 to plug the security hole
# by removing "mpost" from the "shell_escape_commands" variable of default
# texmf configuration.
# However, depending on the customization of a user, he/she can still be
# affected after the update.
#
# To prevent exploitation of the vulnerability, this script checks
# if "mpost" is present in source files of perfbook.
# If the vulnerability is fixed in your TeX environment, the check is
# skipped.
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
#
#-------------------------------------------------------------------
# Instruction to plug the security hole
# (based on http://d.hatena.ne.jp/zrbabbler/20161206/1481039449 (in Japanese),
# translated and supplemented by Akira Yokosawa)
#
# 1. Test the config of your TeX environment
#
# Enter the following in a command shell:
#
#   $ kpsewhich -var-value=shell_escape_commands
#
# Example output:
#
#   bibtex,bibtex8,extractbb,kpsewhich,makeindex,mpost,repstopdf
#
# If "mpost" appears in the output, your setting is vulnerable.
# Following variants of "mpost" are also vulnerable:
#    pmpost
#    jmpost
#    upmpost
#
# Note:
#   "rmpost" and "rpmpost" in the list are known to be safe.
#
# 2. Solution
#
# 2-1. Update TeX distribution if possible
#
#   However, depending on your customization, you may still be vulnerable.
#   Do Step 1 again after the update.
#   If you are still vulnerable, proceed to Step 2-2.
#
# 2-2. Modify texmf configuration
#
# 2-2-1. Using tlmgr
#
#   If tlmgr is available, enter the following command in a command shell:
#
#   $ tlmgr conf texmf shell_escape_commands [list]
#
#   Here, [list] is a command list displayed in Step 1 with "mpost," removed,
#   e.g.:
#
#   $ tlmgr conf texmf shell_escape_commands \
#   > bibtex,bibtex8,extractbb,kpsewhich,makeindex,repstopdf
#
# 2-2-2. Manual fix
#
#  If tlmgr is not available, proceed as follows:
#
#  o Search effective texmf.cnf
#
#   Enter the following command:
#
#   $ kpsewhich texmf.cnf
#
#   The path displayed is the effective one.
#
#  o Edit the texmf.cnf to remove "mpost" from shell_escape_commands
#
#   If there is a line beginning with "shell_escape_commands=" in the
#   texmf.cnf file, edit it to remove "mpost,".
#
#   If there is not such a line, add a line of:
#
#   shell_escape_commands=[list]
#
#   where [list] is again a command list displayed in Step 1 with "mpost,"
#   removed, e.g.:
#
#   shell_escape_commands=bibtex,bibtex8,extractbb,kpsewhich,makeindex,repstopdf
#
# Note:
#   If the effective texmf.cnf has a comment saying not to edit it directly,
#   follow the instruction given there.
#-------------------------------------------------------------------

dogrep() {
	texsrc=`find . -name "*.tex" -print`
	bibsrc=`find . -name "*.bib" -print`
	stysrc=`find . -name "*.sty" -print`
	clssrc=`find . -name "*.cls" -print`
	bstsrc=`find . -name "*.bst" -print`
	perfbooksrc="$texsrc $bibsrc $stysrc $clssrc $bstsrc"
	if grep -w -n "mpost" $perfbooksrc || \
			grep -w -n "[jp]mpost" $perfbooksrc || \
			grep -w -n "upmpost" $perfbooksrc
	then
		echo "#####################################################"
		echo "## 'mpost' is found in LaTeX sources. Aborting...  ##"
		echo "## Refer to comment in utilities/mpostcheck.sh.    ##"
		echo "#####################################################"
		exit 1
	fi
}

if which kpsewhich >/dev/null
then
	command_list=`kpsewhich -var-value=shell_escape_commands`
	if echo $command_list | grep -w -q "mpost" || \
			echo $command_list | grep -w -q "[jp]mpost" || \
			echo $command_list | grep -w -q "upmpost"
	then
		echo "kpsewhich -var-value=shell_escape_commands"
		echo $command_list
		echo "WARNING: Refer to utilities/mpostcheck.sh for texmf config fix."
		dogrep
	else
		exit 0
	fi
else
	dogrep
	exit 0
fi
