/*
 * rcu_nest.h: user-level implementation of RCU permitting nesting.
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

#include "rcu_pointer.h"

/* Borrow from rcupdate.h in Linux kernel */
#define ULONG_CMP_GE(a, b)      (ULONG_MAX / 2 >= (a) - (b))
#define ULONG_CMP_LT(a, b)      (ULONG_MAX / 2 < (a) - (b))

DEFINE_SPINLOCK(rcu_gp_lock);
#define RCU_GP_CTR_SHIFT 7
#define RCU_GP_CTR_BOTTOM_BIT (1 << RCU_GP_CTR_SHIFT)
#define RCU_GP_CTR_NEST_MASK (RCU_GP_CTR_BOTTOM_BIT - 1)
#define MAX_GP_ADV_DISTANCE (RCU_GP_CTR_NEST_MASK << 8)
unsigned long rcu_gp_ctr = 0;	/* increment by RCU_GP_CTR_BOTTOM_BIT each gp. */
DEFINE_PER_THREAD(unsigned long, rcu_reader_gp);

static inline int rcu_gp_ongoing(int cpu)
{
	return per_thread(rcu_reader_gp, cpu) & RCU_GP_CTR_NEST_MASK;
}

static void rcu_init(void)
{
	init_per_thread(rcu_reader_gp, 0);
}

static void rcu_read_lock(void)
{
	unsigned long tmp;
	unsigned long *rrgp;

	/*
	 * If this is the outermost RCU read-side critical section,
	 * copy the global grace-period counter.  In either case,
	 * increment the nesting count held in the low-order bits.
	 */

	rrgp = &__get_thread_var(rcu_reader_gp);
retry:
	tmp = *rrgp;
	if ((tmp & RCU_GP_CTR_NEST_MASK) == 0)
		tmp = READ_ONCE(rcu_gp_ctr);
	tmp++;
	WRITE_ONCE(*rrgp, tmp);
	smp_mb();

	/*
	 * A reader could be suspended in between fetching the value of *rrgp
	 * and writting the updated value back into *rrgp. During this
	 * time period, the grace-period counter might have advanced very far.
	 * In this case, we force the reader to start over. One special case
	 * is that "rcu_gp_ctr" may have wrapped around while "tmp" is close to
	 * ULONG_MAX. To handle this correctly, we adopt the helper function
	 * ULONG_CMP_GE.
	 */

	if (((tmp & RCU_GP_CTR_NEST_MASK) == 1) &&
	     ULONG_CMP_GE(READ_ONCE(rcu_gp_ctr), tmp + MAX_GP_ADV_DISTANCE)) {
		WRITE_ONCE(*rrgp, *rrgp - 1);
		goto retry;
	}
}

static void rcu_read_unlock(void)
{
	/*
	 * Decrement the nesting counter held in the low-order bits,
	 * which had better not initially be zero.
	 */

	smp_mb();
#ifdef DEBUG_EXTREME
	BUG_ON((__get_thread_var(rcu_reader_gp) & RCU_GP_CTR_NEST_MASK) != 0);
#endif /* #ifdef DEBUG_EXTREME */
	__get_thread_var(rcu_reader_gp)--;
}

extern void synchronize_rcu(void);
