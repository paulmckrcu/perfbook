/*
 * seqlock.h: simple user-level sequence locking
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
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

typedef struct {
	unsigned long seq;
	spinlock_t lock;
} seqlock_t;

#define DEFINE_SEQ_LOCK(name) seqlock_t name = { \
	.seq = 0, \
	.lock = __SPIN_LOCK_UNLOCKED(name.lock), \
};

static inline void seqlock_init(seqlock_t *slp)
{
	slp->seq = 0;
	spin_lock_init(&slp->lock);
}

static inline unsigned long read_seqbegin(seqlock_t *slp)
{
	unsigned long s;

	s = READ_ONCE(slp->seq);
	smp_mb();
	return s & ~0x1UL;
}

static inline int read_seqretry(seqlock_t *slp, unsigned long oldseq)
{
	unsigned long s;

	smp_mb();
	s = READ_ONCE(slp->seq);
	return s != oldseq;
}

static inline void write_seqlock(seqlock_t *slp)
{
	spin_lock(&slp->lock);
	++slp->seq;
	smp_mb();
}

static inline void write_sequnlock(seqlock_t *slp)
{
	smp_mb();
	++slp->seq;
	spin_unlock(&slp->lock);
}
