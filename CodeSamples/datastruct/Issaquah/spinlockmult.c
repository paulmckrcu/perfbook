/*
 * spinlockmult.c: Search tree supporting atomic move.
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
 * Copyright (c) 2014-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <sys/time.h>
#include "../../api.h"

/*
 * Acquire multiple spinlocks, sorting to avoid deadlock.  Duplicate
 * locks are acquired only once.
 */
void spin_lock_mult(spinlock_t **lockp, int n)
{
	int i, j;
	spinlock_t *tmp;

	/* Sort.  This code assumes a modest number of locks, like <= 20. */
	for (i = 0; i < n; i++) {
		for (j = i + 1; j < n; j++) {
			if (lockp[i] < lockp[j])
				continue;
			if (lockp[i] == lockp[j]) {
				n--;
				lockp[j] = lockp[n];
				lockp[n] = NULL;
				j--;
				continue;
			}
			tmp = lockp[i];
			lockp[i] = lockp[j];
			lockp[j] = tmp;
		}
		if (lockp[i] != NULL)
			spin_lock(lockp[i]);
	}
}

/*
 * Release the locks acquired by spin_lock_mult().
 */
void spin_unlock_mult(spinlock_t **lockp, int n)
{
	int i;

	for (i = 0; i < n; i++)
		if (lockp[i] != NULL)
			spin_unlock(lockp[i]);
}
