/*
 * log.h: Common definitions for various atomic-append log implementations
 *	Spoiler: Partitioning scales best.
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
 * Copyright (c) 2016-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#define _LGPL_SOURCE
#include "../../api.h"
#include "../../lib/random.h"

/*
 * Log record.
 */
struct log_rec {
	long lr_flags;
	unsigned long lr_value;
};

/*
 * Log header.
 */
struct log_head {
	struct log_rec *lh_log;
	long lh_n_entries;
	spinlock_t lh_lock;
	long lh_next_idx;
};

/* Access functions. */
void log_init(struct log_head *lp, long nrecs);
void log_cleanup(struct log_head *lp);
unsigned long get_log_value(struct log_head *lp, long idx);
long log_append(struct log_head *lp, unsigned long val);
long get_log_next_idx(struct log_head *lp);
