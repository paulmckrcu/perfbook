#!/bin/sh
#
# Extracts Quick Quizzes from the main latex document and transforms
# them to generate an "answers" chapter.
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
# Copyright (C) IBM Corporation, 2008-2019
# Copyright (C) Facebook, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

: ${SED:=sed}
# Requirement: sed with multi-line editing enabled.

echo "% mainfile: perfbook.tex"
$SED -n -e '/^\\QuickQuizChapter{/p' \
        -e '/^\\E\?QuickQuiz[BEM]\?{/,/^}\\E\?QuickQuizEnd[BEM]\?/p' |
$SED -e 's/^\\QuickQuizChapter{/\\QuickQAC{/' \
     -e 's/^\\E\?QuickQuiz[BEM]\?{/\\QuickQ{}/' \
     -e 's/^}\\E\?QuickQuizAnswer[BEM]\?{/\\QuickA{}/' \
     -e 's/^\\QContributedBy{/\\ContributedBy{/' \
     -e 's/^}\\E\?QuickQuizEnd[BEM]\?/\\QuickE{}/'
