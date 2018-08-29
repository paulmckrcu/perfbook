#!/bin/sh
# SPDX-License-Identifier: GPL-2.0
#
# Remove 2nd {} in litmus tests compatible with litmus7:
#    {
#    #include <api.h>
#    }
#
# Borrowed from one of the answers in:
#   https://unix.stackexchange.comm/questions/213385/
# Not the selected answer because it read input file twice.
# But this is easier to follow.
#
# Copyright (C) Akira Yokosawa, 2017
#
# Authors: Akira Yokosawa <akiyks@gmail.com>

grep -n -A1 -B1 "api.h" $1 | \
sed -n 's/^\([0-9]\{1,\}\).*/\1d/p' | \
sed -f - $1 | \
sed -e '/\\begin\[snippet\]/d' | \
sed -e '/\\end\[snippet\]/d' > $2
