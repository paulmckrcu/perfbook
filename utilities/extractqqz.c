/*
 * extractqqz.c: extract QuickQuiz answers from a latex document.
 *	The resulting answers can be included into an "answers" section
 *	of the document.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

/* Also need to follow \input statements.  Which will require making the */
/*  current_line and current_file vars passed through arglists. */
/* Also need to test various combinations... */

#include <stdio.h>
#include <stdlib.h>
#include <strings.h>
#include <string.h>
#include <limits.h>

char *current_file = NULL;
long current_line = 0;

int ignore_line(FILE *fp, char *buf, int bufsiz)
{
	do {
		if (index(buf, '\n'))
			return 1;
	} while (fgets(buf, bufsiz, fp) != NULL);
	return 0;
}

int output_line(FILE *fp, char *buf, int bufsiz)
{
	do {
		if (fputs(buf, stdout) == EOF) {
			fprintf(stderr, "Output error: \"%s\":%d\n",
				current_file, current_line);
			exit(-1);
		}
		if (index(buf, '\n'))
			return 1;
	} while (fgets(buf, bufsiz, fp) != NULL);
	return 0;
}

int output_line_addanswer(FILE *fp, char *buf, int bufsiz, char *outbuf)
{
	char *abp;
	char *ans = "Answer";
	char *bp;
	char *cbp;
	char *obp;

	cbp = index(buf, '{');
	if (cbp == NULL)
		abort();
	for (bp = buf, obp = outbuf; bp < cbp; bp++, obp++)
		*obp = *bp;
	for (abp = ans; *abp; abp++, obp++)
		*obp = *abp;
	for (; *bp; bp++, obp++)
		*obp = *bp;
	*obp = '\0';
	output_line(fp, outbuf, bufsiz);
}

void output_position()
{
	printf("%% %s:%d\n", current_file, current_line);
}

int sc(char *cp, char *ccp, int bufsiz)
{
	int s = strlen(ccp);

	if (s > bufsiz)
		s = bufsiz;
	return (strncmp(cp, ccp, s));
}

#define STATE_SCANNING	0
#define STATE_QQZ	1

void do_one_file(char *fn)
{
	char buf[PATH_MAX + 50];
	char *cp;
	char *fnp = NULL;
	FILE *fp;
	int lastqqz = 0;
	char outbuf[PATH_MAX + 100];
	int state;

	current_file = fn;
	current_line = 0;
	if ((fp = fopen(fn, "r")) == NULL) {
		fnp = malloc(strlen(fn) + 10);
		strcpy(fnp, fn);
		strcat(fnp, ".tex");
		current_file = fnp;
		if ((fp = fopen(fnp, "r")) == NULL) {
			current_file = fn;
			perror(fn);
			goto outerr;
		}
	}
	state = STATE_SCANNING;
	while ((cp = fgets(buf, sizeof(buf), fp)) != NULL) {
		current_line++;
		if (state == STATE_QQZ) {
			if (sc(buf, "\\QuickQuizEnd", sizeof(buf)) == 0) {
				state = STATE_SCANNING;
				ignore_line(fp, buf, sizeof(buf));
				continue;
			}
			if ((sc(buf, "\\QuickQuiz{", sizeof(buf)) == 0) ||
			    (sc(buf, "\\QuickQuizChapter{", sizeof(buf)) == 0)) {
				fprintf(stderr, "%s:%d: Bad directive\n",
					current_file, current_line);
				goto outerr;
			}
			output_line(fp, buf, sizeof(buf));
			continue;
		}
		/* state == STATE_SCANNING */
		if (sc(buf, "\\QuickQuizChapter{", sizeof(buf)) == 0) {
			output_line_addanswer(fp, buf, sizeof(buf), outbuf);
			continue;
		}
		if (sc(buf, "\\QuickQuiz{", sizeof(buf)) == 0) {
			state = STATE_QQZ;
			lastqqz = current_line;
			output_position();
			output_line_addanswer(fp, buf, sizeof(buf), outbuf);
			continue;
		}
		if (sc(buf, "\\QuickQuizEnd", sizeof(buf)) == 0) {
			fprintf(stderr, "%s:%d: Bad directive\n",
				current_file, current_line);
			goto outerr;
		}
		if (sc(buf, "\\input", sizeof(buf)) == 0) {
			char *opencurly = index(buf, '{');
			char *closecurly = index(buf, '}');
			char *savefn = current_file;
			int saveline = current_line;

			if (opencurly == NULL || closecurly == NULL) {
				fprintf(stderr,
					"%s:%d: Malformed \\input{path}\n",
					current_file, current_line);
				goto outerr;
			}
			*closecurly = '\0';
			do_one_file(opencurly + 1);
			*closecurly = '}';
			current_file = savefn;
			current_line = saveline;
		}
		ignore_line(fp, buf, sizeof(buf));
	}
	if (state != STATE_SCANNING) {
		fprintf(stderr,
			"%s:%d: \\QuickQuiz without \\QuickQuizEnd\n",
			current_file, lastqqz);
	}
	if (fnp != NULL)
		free(fnp);
	return;
outerr:
	if (fnp != NULL)
		free(fnp);
	exit(-1);
}

int main(int argc, char *argv[])
{
	int i;

	for (i = 1; i < argc; i++)
		do_one_file(argv[i]);

	return 0;
}
