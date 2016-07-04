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
# Copyright (C) IBM Corporation, 2008
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>

sed -n -e '/^\\QuickQuizChapter{/p' \
       -e '/^\\QuickQuiz{/,/^} \\QuickQuizEnd/p' |
sed -e 's/^\\QuickQuizChapter{/\\QuickQAC{/' \
    -e 's/^\\QuickQuiz{/\\QuickQ{/' \
    -e 's/^\\QuickQuizAnswer{/\\QuickA{}/' \
    -e 's/^\\QContributedBy{/\\ContributedBy{/' \
    -e 's/^} \\QuickQuizEnd/\\QuickE{}/'
