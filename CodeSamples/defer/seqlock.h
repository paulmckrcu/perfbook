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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

typedef struct {
	unsigned long seq;
	spinlock_t lock;
} seqlock_t;

static void seqlock_init(seqlock_t *slp)
{
	slp->seq = 0;
	spin_lock_init(&slp->lock);
}

static unsigned long read_seqbegin(seqlock_t *slp)
{
	unsigned long s;

repeat:
	s = ACCESS_ONCE(slp->seq);
	smp_mb();
	if (unlikely(s & 1))
		goto repeat;
	return s;
}

static int read_seqretry(seqlock_t *slp, unsigned long oldseq)
{
	unsigned long s;

	smp_mb();
	s = ACCESS_ONCE(slp->seq);
	return s != oldseq;
}

static void write_seqlock(seqlock_t *slp)
{
	spin_lock(&slp->lock);
	++slp->seq;
	smp_mb();
}

static void write_sequnlock(seqlock_t *slp)
{
	smp_mb();
	++slp->seq;
	spin_unlock(&slp->lock);
}
