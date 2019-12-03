/*
 * rcu.c: simple user-level implementation of RCU.
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

#include "../api.h"
#include "rcu.h"

//\begin{snippet}[labelbase=ln:defer:rcu:synchronize,gobbleblank=yes,commandchars=\%\@\$]
void synchronize_rcu(void)			//\lnlbl{syn:b}
{
	int t;
							//\fcvblank
	/* Memory barrier ensures mutation seen before grace period. */

	smp_mb();				//\lnlbl{syn:mb1}

	/* Only one synchronize_rcu() at a time. */

	spin_lock(&rcu_gp_lock);		//\lnlbl{syn:spinlock}

	/* Advance to a new grace-period number, enforce ordering. */

	WRITE_ONCE(rcu_gp_ctr, rcu_gp_ctr + 2); //\lnlbl{syn:increasegp}
	smp_mb();				//\lnlbl{syn:mb2}

	/*
	 * Wait until all threads are either out of their RCU read-side
	 * critical sections or are aware of the new grace period.
	 */

	for_each_thread(t) {			//\lnlbl{syn:scan:b}
		while ((per_thread(rcu_reader_gp, t) & 0x1) &&//\lnlbl{syn:even}
		       ((per_thread(rcu_reader_gp, t) -	//\lnlbl{syn:gt1}
		         rcu_gp_ctr) < 0)) {		//\lnlbl{syn:gt2}
#ifndef FCV_SNIPPET
			/*@@@ poll(NULL, 0, 10); */
			barrier();
#else
			poll(NULL, 0, 10);	//\lnlbl{syn:poll}
#endif
		}
	}					//\lnlbl{syn:scan:e}

	/* Let other synchronize_rcu() instances move ahead. */

	spin_unlock(&rcu_gp_lock);		//\lnlbl{syn:spinunlock}

	/* Ensure that any subsequent free()s happen -after- above checks. */

	smp_mb();				//\lnlbl{syn:mb3}
}						//\lnlbl{syn:e}
//\end{snippet}
#ifdef TEST
#include "rcutorture.h"
#endif /* #ifdef TEST */
