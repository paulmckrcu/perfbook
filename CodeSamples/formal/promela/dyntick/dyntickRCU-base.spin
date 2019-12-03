/*
 * Tests a variation of RCU-dyntick interaction in the Linux 2.6.25-rc4
 * kernel.  Note that portions of this are derived from Linux kernel code,
 * portions of which are licensed under a GPLv2-only license.
 *
 * This version omits irq/NMI handlers.  It does not have either safety
 * or liveness checks.
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
 * Copyright (c) 2019 Facebook.
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
 * Validation code for the slice of the preemptible-RCU code that
 * interacts with the dynticks subsystem.  This is set up to match
 * the code in 2.6.25-rc4, namely dyntick_save_progress_counter(),
 * rcu_try_flip_waitack_needed(), rcu_try_flip_waitmb_needed(),
 * and portions of rcu_try_flip_waitack() and rcu_try_flip_waitmb().
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-base:grace_period,style=N,gobbleblank=yes,commandchars=\@\[\]]
proctype grace_period()
{
	byte curr;
	byte snap;
								//\fcvblank
	/*
	 * A little code from rcu_try_flip_idle() and its call
	 * to dyntick_save_progress_counter().
	 */

	atomic {					//\lnlbl{print:b}
#ifndef FCV_SNIPPET
		printf("MAX_DYNTICK_LOOP_NOHZ = %d\n", MAX_DYNTICK_LOOP_NOHZ);
#else /* #ifndef FCV_SNIPPET */
		printf("MDLN = %d\n", MAX_DYNTICK_LOOP_NOHZ);
#endif /* #ifndef FCV_SNIPPET */
		snap = dynticks_progress_counter;
	}						//\lnlbl{print:e}

	/*
	 * Each pass through the following loop corresponds to an
	 * invocation of the scheduling-clock interrupt handler,
	 * specifically a little code from rcu_try_flip_waitack()
	 * and its call to rcu_try_flip_waitack_needed().
	 */

	do						//\lnlbl{do1}
	:: 1 ->
		atomic {
			curr = dynticks_progress_counter;
			if
			:: (curr == snap) && ((curr & 1) == 0) ->
				break;
			:: (curr - snap) > 2 || (snap & 1) == 0 ->
				break;
			:: 1 -> skip;
			fi;
		}
	od;						//\lnlbl{od1}

	/*
	 * A little code from rcu_try_flip_waitzero() and its call
	 * to dyntick_save_progress_counter(), plus a bunch of
	 * validation code.
	 */

	snap = dynticks_progress_counter;		//\lnlbl{snap}

	/*
	 * Each pass through the following loop corresponds to an
	 * invocation of the scheduling-clock interrupt handler,
	 * specifically a little code from rcu_try_flip_waitmb()
	 * and its call to rcu_try_flip_waitmb_needed().
	 */

	do						//\lnlbl{do2}
	:: 1 ->
		atomic {
			curr = dynticks_progress_counter;
			if
			:: (curr == snap) && ((curr & 1) == 0) ->
				break;
			:: (curr != snap) ->
				break;
			:: 1 -> skip;
			fi;
		}
	od;						//\lnlbl{od2}
}
//\end{snippet}

/*
 * Validation code for the rcu_enter_nohz() and rcu_exit_nohz()
 * functions.  Each pass through this process's loop corresponds
 * to exiting nohz mode, then re-entering it.  This code also
 * includes assertions corresponding to the WARN_ON() calls in
 * rcu_exit_nohz() and rcu_enter_nohz().
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-base:dyntick_nohz,style=N,gobbleblank=yes,commandchars=\\\[\]]
proctype dyntick_nohz()
{
	byte tmp;
	byte i = 0;
								//\fcvblank
	do						//\lnlbl{do}
	:: i >= MAX_DYNTICK_LOOP_NOHZ -> break;		//\lnlbl{break}
	:: i < MAX_DYNTICK_LOOP_NOHZ ->			//\lnlbl{kick_loop}

		/*
		 * The following corresponds to rcu_exit_nohz().
		 */

		tmp = dynticks_progress_counter;	//\lnlbl{ex_inc:b}
		atomic {
			dynticks_progress_counter = tmp + 1; //\lnlbl{ex_inc:e}
			assert((dynticks_progress_counter & 1) == 1); //\lnlbl{ex_assert}
		}

		/*
		 * The following corresponds to rcu_enter_nohz().
		 */

		tmp = dynticks_progress_counter;	//\lnlbl{ent_inc:b}
		atomic {
			dynticks_progress_counter = tmp + 1;
			assert((dynticks_progress_counter & 1) == 0);
		}					//\lnlbl{ent_inc:e}
		i++;					//\lnlbl{inc_i}
	od;						//\lnlbl{od}
}
//\end{snippet}

init {
	atomic {
		run dyntick_nohz();
		run grace_period();
	}
}
