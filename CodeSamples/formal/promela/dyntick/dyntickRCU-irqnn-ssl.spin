/*
 * Tests a variation of RCU-dyntick interaction in the Linux 2.6.25-rc4
 * kernel.  Note that portions of this are derived from Linux kernel code,
 * portions of which are licensed under a GPLv2-only license.
 *
 * This version omits NMI handlers, and disallows nested irq handlers.
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
 * MAX_DYNTICK_LOOP_IRQ: The number of interrupts (possibly arbitrarily
 *	nested) to be received.
 *
 * Setting a given value for a given parameter covers all values up to
 * and including the specified value.  So, if MAX_DYNTICK_LOOP_IRQ is
 * set to "2", then the validation will cover 0, 1, and 2 interrupts.
 */

#define MAX_DYNTICK_LOOP_NOHZ 3
#define MAX_DYNTICK_LOOP_IRQ 3

/* Variables corresponding to the 2.6.25-rc4 per-CPU variables. */

byte dynticks_progress_counter = 0;
byte rcu_update_flag = 0;
byte in_interrupt = 0;

/* Set when IRQ code is running, to allow mainline code to lock itself out. */

bit in_dyntick_irq = 0;

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
bit dyntick_irq_done = 0;

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

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irqnn-ssl:grace_period,style=N,gobbleblank=yes,commandchars=\@\[\]]
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
		printf("MAX_DYNTICK_LOOP_IRQ = %d\n", MAX_DYNTICK_LOOP_IRQ);
#else /* #ifndef FCV_SNIPPET */
		printf("MDLN = %d\n", MAX_DYNTICK_LOOP_NOHZ);
		printf("MDLI = %d\n", MAX_DYNTICK_LOOP_IRQ); //\lnlbl{MDLI}
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
			shouldexit = dyntick_nohz_done && dyntick_irq_done; //\lnlbl{edit1}
			curr = dynticks_progress_counter;
			if
			:: (curr - snap) >= 2 || (curr & 1) == 0 -> //\lnlbl{edit2}
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
			shouldexit = dyntick_nohz_done && dyntick_irq_done; //\lnlbl{edit3}
			curr = dynticks_progress_counter;
			if
			:: (curr != snap) || ((curr & 1) == 0) -> //\lnlbl{edit4}
				break;
			:: else -> skip;
			fi;
		}
	od;
	grace_period_state = GP_DONE;
}
//\end{snippet}

/*
 * Macro that allows dyntick_irq() code to run atomically with respect
 * to dyntick_nohz(), but still allows dyntick_irq() to be interleaved
 * with other processes.
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irqnn-ssl:EXECUTE_MAINLINE,style=N,commandchars=\@\[\]]
#define EXECUTE_MAINLINE(label, stmt) \
label: skip;  /* \lnlbl{label} */\
		atomic { /* \lnlbl{atm:b} */\
			if \
			:: in_dyntick_irq -> goto label; \
			:: else -> stmt; /* \lnlbl{else} */\
			fi; \
		} /* \lnlbl{atm:e} */
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

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irqnn-ssl:dyntick_nohz,style=N,gobbleblank=yes,commandchars=\\\[\]]
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

		EXECUTE_MAINLINE(stmt1,
			tmp = dynticks_progress_counter)
		EXECUTE_MAINLINE(stmt2, /* \lnlbl{stmt2:b} */
			dynticks_progress_counter = tmp + 1;
			old_gp_idle = (grace_period_state == GP_IDLE);
			assert((dynticks_progress_counter & 1) == 1)) /* \lnlbl{stmt2:e} */

		/*
		 * The following corresponds to rcu_enter_nohz(), along
		 * with code to check for grace_period() jumping the gun.
		 */

		EXECUTE_MAINLINE(stmt3,
			tmp = dynticks_progress_counter;
			assert(!old_gp_idle ||
			       grace_period_state != GP_DONE))
		EXECUTE_MAINLINE(stmt4,
			dynticks_progress_counter = tmp + 1;
			assert((dynticks_progress_counter & 1) == 0))
		i++;
	od;
	dyntick_nohz_done = 1;
}
//\end{snippet}

/*
 * Validation code corresponding to rcu_irq_enter() and rcu_irq_exit().
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irqnn-ssl:dyntick_irq,style=N,gobbleblank=yes,commandchars=\\\[\]]
proctype dyntick_irq()
{
	byte tmp;
	byte i = 0;
	bit old_gp_idle;
								//\fcvblank
	do						//\lnlbl{do}
	:: i >= MAX_DYNTICK_LOOP_IRQ -> break;		//\lnlbl{cond1}
	:: i < MAX_DYNTICK_LOOP_IRQ ->			//\lnlbl{cond2}

		/* Tell dyntick_nohz() that we are in interrupt handler. */

		in_dyntick_irq = 1;			//\lnlbl{in_irq}

		/* Validation code corresponding to rcu_irq_enter(). */

		if					//\lnlbl{enter:b}
		:: rcu_update_flag > 0 ->
			tmp = rcu_update_flag;
			rcu_update_flag = tmp + 1;
		:: else -> skip;
		fi;
		if
		:: !in_interrupt &&
		   (dynticks_progress_counter & 1) == 0 ->
			tmp = dynticks_progress_counter;
			dynticks_progress_counter = tmp + 1;
			tmp = rcu_update_flag;
			rcu_update_flag = tmp + 1;
		:: else -> skip;
		fi;					//\lnlbl{enter:e}

		/* 
		 * And a snippet from __irq_enter() corresponding to
		 * the add_preempt_count().
		 */

		tmp = in_interrupt;			//\lnlbl{add_prmt_cnt:b}
		in_interrupt = tmp + 1;			//\lnlbl{add_prmt_cnt:e}

		/* Capture state to see if grace_period() is behaving. */

		old_gp_idle = (grace_period_state == GP_IDLE); //\lnlbl{vrf_safe:b}

		/* See if we can catch grace_period() misbehaving. */

		assert(!old_gp_idle ||
		       grace_period_state != GP_DONE);	//\lnlbl{vrf_safe:e}

		/*
		 * Validation code corresponding to the sub_preempt_count()
		 * in __irq_exit().
		 */

		tmp = in_interrupt;			//\lnlbl{irq_exit:b}
		in_interrupt = tmp - 1;			//\lnlbl{irq_exit:e}

		/* Validation code corresponding to rcu_irq_exit(). */

		if					//\lnlbl{exit:b}
		:: rcu_update_flag != 0 ->
			tmp = rcu_update_flag;
			rcu_update_flag = tmp - 1;
			if
			:: rcu_update_flag == 0 ->
				tmp = dynticks_progress_counter;
				dynticks_progress_counter = tmp + 1;
			:: else -> skip;
			fi;
		:: else -> skip;
		fi;					//\lnlbl{exit:e}

		/*
		 * Count the exit and let dyntick_nohz() know if we
		 * have completely exited a nested set of interrupts.
		 * Count the irq handler for termination.
		 */

		atomic {
			in_dyntick_irq = 0;		//\lnlbl{clr_in_irq}
			i++;				//\lnlbl{inc_i}
		}
	od;						//\lnlbl{od}
	dyntick_irq_done = 1;				//\lnlbl{irq_done}
}
//\end{snippet}

init {
	atomic {
		run dyntick_nohz();
		run dyntick_irq();
		run grace_period();
	}
}
