/*
 * rcu_lock.h: simple user-level implementation of RCU based on locking.
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

#include "rcu_pointer.h"

DEFINE_SPINLOCK(rcu_gp_lock);

static void rcu_init(void)
{
}

static void rcu_read_lock(void)
{
	spin_lock(&rcu_gp_lock);
}

static void rcu_read_unlock(void)
{
	spin_unlock(&rcu_gp_lock);
}

extern void synchronize_rcu(void);
