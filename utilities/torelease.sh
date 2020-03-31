#!/bin/sh
#
# torelease.sh: Produce release work products for perfbook, including
#	PDFs and changelog.
#
# Usage torelease.sh [ destdir [ "Edition tag" [ repo_url [ remote ] ] ] ]
#
# The destination directory defaults to /tmp, and the edition tag
# defaults to being a release tag, as in v2019.12.22a.  Edition tags
# have the form "Edition.1", "Edition.1P", or "Edition.1P-rc3".
# "repo_url" defaults to Paul's git repository at gitolite.kernel.org.
# "remote" defaults to "origin".
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
# Copyright (C) Paul E. McKenney, 2019
#
# Authors: Paul E. McKenney <paulmck@kernel.org>

# Make sure the build scripts behave as expected
unset PERFBOOK_DEFAULT
unset PERFBOOK_PAPER

destdir="${1-/tmp}"
tag="${2-`date +%Y.%m.%d`a}"
repo_url=${3-git@gitolite.kernel.org:pub/scm/linux/kernel/git/paulmck/perfbook.git}
remote=${4-origin}

if ! test -d "${destdir}" -o ! -w "${destdir}"
then
	echo Bogus destination directory, giving up.
	exit 1
fi
if ! git status --porcelain > /dev/null 2>&1
then
	echo Git repository nonexistent or in bad shape, giving up.
	exit 2
fi
if test -n "`git status --porcelain`"
then
	git status
	echo Git repository working tree not clean, giving up.
	exit 3
fi

oldtag="`git describe --tags HEAD | sed -e 's/-.*$//'`"
case "${tag}" in
[0-9]*)
	gittag=v${tag}
	;;
*)
	gittag=${tag}
	;;
esac
if git tag -l | grep -q "\^${gittag}\$"
then
	echo Tag ${gittag} already exists, giving up.
	exit 4
fi
if ! git tag "${gittag}"
then
	echo "Giving up."
	exit 5
fi
touch perfbook.tex # Force re-run of "utilities/autodate.sh"

if ! make
then
	git tag -d "${gittag}"
	echo Double-column build failed, giving up.
	exit 6
fi
cp perfbook.pdf "${destdir}/perfbook.${tag}.pdf"

if ! make 1c
then
	git tag -d "${gittag}"
	echo Single-column build failed, giving up.
	exit 7
fi
cp perfbook-1c.pdf "${destdir}/perfbook-1c.${tag}.pdf"

# Yes, this will ask for credentials for the remote repository...
# If this becomes too irritating, a replacement script can be created.
if ! git push ${remote} ${gittag}
then
	git tag -d ${gittag}
	echo Tag push failed, giving up.
	exit 8
fi
git request-pull ${oldtag} ${repo_url} ${gittag} | sed -n '/^--*$/,$p' | tail +2 > "${destdir}/Changes.${tag}.txt"

ls -l "${destdir}/perfbook.${tag}.pdf" "${destdir}/perfbook-1c.${tag}.pdf" "${destdir}/Changes.${tag}.txt"
echo Release v${tag} prepared in ${destdir}
exit 0
