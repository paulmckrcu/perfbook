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
 * Copyright (c) 2008-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

//\begin{snippet}[labelbase=ln:defer:seqlock:impl,commandchars=\\\[\]]
typedef struct {				//\lnlbl{typedef:b}
	unsigned long seq;			//\lnlbl{typedef:seq}
	spinlock_t lock;
} seqlock_t;					//\lnlbl{typedef:e}

#ifndef FCV_SNIPPET
#define DEFINE_SEQ_LOCK(name) seqlock_t name = { \
	.seq = 0,                                \
	.lock = __SPIN_LOCK_UNLOCKED(name.lock), \
};
#endif /* FCV_SNIPPET */
							//\fcvexclude
static inline void seqlock_init(seqlock_t *slp)		//\lnlbl{init:b}
{
	slp->seq = 0;
	spin_lock_init(&slp->lock);
}							//\lnlbl{init:e}

static inline unsigned long read_seqbegin(seqlock_t *slp) //\lnlbl{read_seqbegin:b}
{
	unsigned long s;

	s = READ_ONCE(slp->seq);			//\lnlbl{read_seqbegin:fetch}
	smp_mb();					//\lnlbl{read_seqbegin:mb}
	return s & ~0x1UL;				//\lnlbl{read_seqbegin:ret}
}							//\lnlbl{read_seqbegin:e}

static inline int read_seqretry(seqlock_t *slp,		//\lnlbl{read_seqretry:b}
                                unsigned long oldseq)
{
	unsigned long s;

	smp_mb();					//\lnlbl{read_seqretry:mb}
	s = READ_ONCE(slp->seq);			//\lnlbl{read_seqretry:fetch}
	return s != oldseq;				//\lnlbl{read_seqretry:ret}
}							//\lnlbl{read_seqretry:e}

static inline void write_seqlock(seqlock_t *slp)	//\lnlbl{write_seqlock:b}
{
	spin_lock(&slp->lock);
	++slp->seq;
	smp_mb();
}							//\lnlbl{write_seqlock:e}

static inline void write_sequnlock(seqlock_t *slp)	//\lnlbl{write_sequnlock:b}
{
	smp_mb();					//\lnlbl{write_sequnlock:mb}
	++slp->seq;					//\lnlbl{write_sequnlock:inc}
	spin_unlock(&slp->lock);
}							//\lnlbl{write_sequnlock:e}
//\end{snippet}
