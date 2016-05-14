/*
 * skiplist.h: Common definitions for simple RCU-protected concurrent skiplists.
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
 * Copyright (c) 2016 Paul E. McKenney, IBM Corporation.
 */

#define _LGPL_SOURCE
#include "../../api.h"

// Uncomment to enable signal-based RCU.  (Need corresponding Makefile change!)
#define RCU_SIGNAL
#include <urcu.h>

// Uncomment to enable QSBR.  (Need corresponding Makefile change!)
//#include <urcu-qsbr.h>

#define SL_MAX_LEVELS 8

struct skiplist {
	int sl_toplevel;
	spinlock_t sl_lock;
	int sl_deleted;
	struct skiplist *sl_head;
	struct skiplist *sl_next[SL_MAX_LEVELS];
};

static int debug;

/*
 * Initialize a skiplist header.
 */
void skiplist_init(struct skiplist *slp)
{
	int i;

	slp->sl_toplevel = SL_MAX_LEVELS - 1;
	spin_lock_init(&slp->sl_lock);
	slp->sl_deleted = 0;
	slp->sl_head = slp;
	for (i = 0; i < SL_MAX_LEVELS; i++)
		slp->sl_next[i] = NULL;
}

/*
 * Pick a random level for a new element.  Exponential power-of-two decrease
 * in probability for higher levels.  Top level gets double expected
 * probability due to truncation, which is in turn due to a finite number
 * of levels.
 */
static int random_level(void)
{
	int i = 0;
	unsigned long r = random();

	while (r & 0x1) {
		i++;
		r >>= 1;
	}
	if (i >= SL_MAX_LEVELS)
		return SL_MAX_LEVELS - 1;
	return i;
}

/*
 * Consistency check for specified element against downstream elements.
 * Make sure lower-level list is connected to each downstream element,
 * and that the downstream element is tall enough.
 */
void skiplist_fsck_one(struct skiplist *first_slp,
		       int (*cmp)(struct skiplist *slp, void *key))
{
	int i;
	struct skiplist *slp;

	slp = first_slp->sl_next[0];
	for (i = 1; i <= first_slp->sl_toplevel; i++) {
		while (slp != first_slp->sl_next[i]) {
			assert(slp);
			slp = slp->sl_next[0];
		}
		assert(!slp || slp->sl_toplevel >= i);
	}
	for (; i < SL_MAX_LEVELS; i++)
		assert(!first_slp->sl_next[i]);
}

/*
 * Consistency check specified skiplist.
 */
void skiplist_fsck(struct skiplist *head_slp,
		   int (*cmp)(struct skiplist *slp, void *key))
{
	struct skiplist *slp;

	for (slp = head_slp; slp; slp = slp->sl_next[0]) {
		skiplist_fsck_one(slp, cmp);
		BUG_ON(slp->sl_head != head_slp);
	}
}
