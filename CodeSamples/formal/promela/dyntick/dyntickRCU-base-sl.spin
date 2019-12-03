/*
 * Tests a variation of RCU-dyntick interaction in the Linux 2.6.25-rc4
 * kernel.  Note that portions of this are derived from Linux kernel code,
 * portions of which are licensed under a GPLv2-only license.
 *
 * This version omits irq/NMI handlers.
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
 * Copyright (c) 2008-2019 IBM Corporation.
 * Copyright (c) Facebook, 2019
 */

/*
 * Parameters:
 *
 * MAX_DYNTICK_LOOP_NOHZ: The number of non-idle process level bursts
 *	of work.
 *
 * Setting a given value for a given parameter covers all values up to
 * and including the specified value.  So, if MAX_DYNTICK_LOOP_NOHZ is
 * set to "2", then the validation will cover 0, 1, and 2 loops.
 */

#define MAX_DYNTICK_LOOP_NOHZ 3

/* Variables corresponding to the 2.6.25-rc4 per-CPU variables. */

byte dynticks_progress_counter = 0;
byte rcu_update_flag = 0;
byte in_interrupt = 0;

/*
 * The grace_period() process uses this to track its progress through
 * each phase, thus allowing the other processes to make sure that
 * grace_period() does not advance prematurely.
 */

#define GP_IDLE		0
#define GP_WAITING	1
#define GP_DONE		2
byte grace_period_state = GP_DONE;

/*
 * The following variables mark completion of the corresponding processes.
 * This is used in grace_period() to check forward progress guarantees.
 */

bit dyntick_nohz_done = 0;

/*
 * Validation code for the slice of the preemptible-RCU code that
 * interacts with the dynticks subsystem.  This is set up to match
 * the code in 2.6.25-rc4, namely dyntick_save_progress_counter(),
 * rcu_try_flip_waitack_needed(), rcu_try_flip_waitmb_needed(),
 * and portions of rcu_try_flip_waitack() and rcu_try_flip_waitmb().
 *
 * This code verifies forward progress: once all of the other processes
 * have terminated, the grace_period() code must not block.  In addition,
 * this code maintains a progress indicator in the grace_period_state
 * variable.  It is an error for grace_period() to advance from GP_IDLE
 * to GP_DONE unless all the other processes are simultaneously in nohz
 * mode at some point during the transition.
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-base-sl:grace_period,style=N,gobbleblank=yes,commandchars=\@\[\]]
proctype grace_period()
{
	byte curr;
	byte snap;
	bit shouldexit;
								//\fcvblank
	/*
	 * A little code from rcu_try_flip_idle() and its call
	 * to dyntick_save_progress_counter(), plus a bunch of
	 * validation code.  The shouldexit variable is for the
	 * later liveness checks.  As noted earlier, the
	 * grace_period_state variable allows the other processes
	 * to scream if we jump the gun here.
	 */

	grace_period_state = GP_IDLE;
	atomic {
#ifndef FCV_SNIPPET
		printf("MAX_DYNTICK_LOOP_NOHZ = %d\n", MAX_DYNTICK_LOOP_NOHZ);
#else /* #ifndef FCV_SNIPPET */
		printf("MDLN = %d\n", MAX_DYNTICK_LOOP_NOHZ);
#endif /* #ifndef FCV_SNIPPET */
		shouldexit = 0;
		snap = dynticks_progress_counter;
		grace_period_state = GP_WAITING;
	}

	/*
	 * Each pass through the following loop corresponds to an
	 * invocation of the scheduling-clock interrupt handler,
	 * specifically a little code from rcu_try_flip_waitack()
	 * and its call to rcu_try_flip_waitack_needed().  The shouldexit
	 * check ensures that we scream if we cannot immediately exit
	 * the loop after all other proceses have completed.
	 */

	do
	:: 1 ->
		atomic {
			assert(!shouldexit);
			shouldexit = dyntick_nohz_done;
			curr = dynticks_progress_counter;
			if
			:: (curr - snap) >= 2 || (curr & 1) == 0 ->
				break;
			:: else -> skip;
			fi;
		}
	od;
	grace_period_state = GP_DONE;

	/*
	 * A little code from rcu_try_flip_waitzero() and its call
	 * to dyntick_save_progress_counter(), plus a bunch of
	 * validation code.  The shouldexit variable is for the
	 * later liveness checks.  As noted earlier, the
	 * grace_period_state variable allows the other processes
	 * to scream if we jump the gun here.
	 */

	grace_period_state = GP_IDLE;
	atomic {
		shouldexit = 0;
		snap = dynticks_progress_counter;
		grace_period_state = GP_WAITING;
	}

	/*
	 * Each pass through the following loop corresponds to an
	 * invocation of the scheduling-clock interrupt handler,
	 * specifically a little code from rcu_try_flip_waitmb()
	 * and its call to rcu_try_flip_waitmb_needed().  The shouldexit
	 * check again ensures that we scream if we cannot immediately exit
	 * the loop after all other proceses have completed.
	 */

	do
	:: 1 ->
		atomic {
			assert(!shouldexit);
			shouldexit = dyntick_nohz_done;
			curr = dynticks_progress_counter;
			if
			:: (curr != snap) || ((curr & 1) == 0) ->
				break;
			:: else -> skip;
			fi;
		}
	od;
	grace_period_state = GP_DONE;
}
//\end{snippet}

/*
 * Validation code for the rcu_enter_nohz() and rcu_exit_nohz()
 * functions.  Each pass through this process's loop corresponds
 * to exiting nohz mode, then re-entering it.  The old_gp_idle
 * variable is used to verify that grace_period() does not incorrectly
 * advance while this process is not in nohz mode.  This code also
 * includes assertions corresponding to the WARN_ON() calls in
 * rcu_exit_nohz() and rcu_enter_nohz().
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-base-sl:dyntick_nohz,style=N,gobbleblank=yes,commandchars=\@\[\]]
proctype dyntick_nohz()
{
	byte tmp;
	byte i = 0;
	bit old_gp_idle;
								//\fcvblank
	do
	:: i >= MAX_DYNTICK_LOOP_NOHZ -> break;
	:: i < MAX_DYNTICK_LOOP_NOHZ ->

		/*
		 * The following corresponds to rcu_exit_nohz(), along
		 * with code to check for grace_period() jumping the gun.
		 */

		tmp = dynticks_progress_counter;
		atomic {
			dynticks_progress_counter = tmp + 1;
			old_gp_idle = (grace_period_state == GP_IDLE);
			assert((dynticks_progress_counter & 1) == 1);
		}

		/*
		 * The following corresponds to rcu_enter_nohz(), along
		 * with code to check for grace_period() jumping the gun.
		 */

		atomic {
			tmp = dynticks_progress_counter;
			assert(!old_gp_idle ||
			       grace_period_state != GP_DONE);
		}
		atomic {
			dynticks_progress_counter = tmp + 1;
			assert((dynticks_progress_counter & 1) == 0);
		}
		i++;
	od;
	dyntick_nohz_done = 1;				//\lnlbl{done}
}
//\end{snippet}

init {
	atomic {
		run dyntick_nohz();
		run grace_period();
	}
}
