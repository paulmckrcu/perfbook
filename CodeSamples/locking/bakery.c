@@@ Test.  Add barriers.
/*
 * bakery.c: Lamport's bakery lock
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
 * Copyright (c) 2010-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

typedef struct {
	int *flag;
	unsigned long *label;
	int n;
} bakerylock_t;

void bakerylock_init(bakerylock_t *blp, int n)
{
	blp->n = n;
	blp->flag = malloc(sizeof(*flag) * n);
	blp->label = malloc(sizeof(*label) * n);
	if (blp->flag == NULL || blp->label == NULL) {
		printf("out of memory\n");
		exit(EXIT_FAILURE);
	}
}

void bakery_lock(bakerylock_t *blp, int me)
{
	int i;
	int max;
	unsigned long maxv;
	unsigned long otherlabel;

	flag[me] = 1;
	smp_mb();
	max = label[0];
	for (i = 1; i < blp->n; i++) {
		maxv = ACCESS_ONCE(label[i]);
		if (maxv > max)
			max = maxv;
	}
	maxv++;
	label[me] = maxv;
	smp_mb();
retry:
	for (i = 0; i < blp->n; i++) {
		if (i == me)
			continue;
		otherlabel = ACCESS_ONCE(label[i]);
		if (ACCESS_ONCE(flag[i]) &&
		    (otherlabel < maxv ||
		     otherlabel == maxv && i < me))
		     	goto retry;
	}
	smp_mb();
}

void bakery_unlock(bakerylock_t *blp, int me)
{
	smp_mb();
	ACCESS_ONCE(flag[me]) = 0;
}
