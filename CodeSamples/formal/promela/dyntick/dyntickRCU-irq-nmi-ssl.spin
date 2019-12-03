/*
 * Tests a variation of RCU-dyntick interaction in the Linux 2.6.25-rc4
 * kernel.  Note that portions of this are derived from Linux kernel code,
 * portions of which are licensed under a GPLv2-only license.
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
 * MAX_DYNTICK_LOOP_NMI: The number of NMIs (never nested) to be received.
 *
 * Setting a given value for a given parameter covers all values up to
 * and including the specified value.  So, if MAX_DYNTICK_LOOP_IRQ is
 * set to "2", then the validation will cover 0, 1, and 2 interrupts,
 * arbitrarily nested.
 */

#define MAX_DYNTICK_LOOP_NOHZ 1
#define MAX_DYNTICK_LOOP_IRQ 2
#define MAX_DYNTICK_LOOP_NMI 1

/* Variables corresponding to the 2.6.25-rc4 per-CPU variables. */

byte dynticks_progress_counter = 0;
byte rcu_update_flag = 0;
byte in_interrupt = 0;

/* Set when IRQ code is running, to allow mainline code to lock itself out. */

bit in_dyntick_irq = 0;

/*
 * Set when NMI code is running, to allow both mainline code and irq handler
 * code to lock itself out.
 */

bit in_dyntick_nmi = 0;

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
bit dyntick_nmi_done = 0;

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

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irq-nmi-ssl:grace_period,gobbleblank=yes,style=N,commandchars=\@\[\]]
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
		printf("MAX_DYNTICK_LOOP_NMI = %d\n", MAX_DYNTICK_LOOP_NMI);
#else /* #ifndef FCV_SNIPPET */
		printf("MDL_NOHZ = %d\n", MAX_DYNTICK_LOOP_NOHZ);
		printf("MDL_IRQ = %d\n", MAX_DYNTICK_LOOP_IRQ);
		printf("MDL_NMI = %d\n", MAX_DYNTICK_LOOP_NMI); //\lnlbl{MDL_NMI}
#endif  /* #ifndef FCV_SNIPPET */
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
			shouldexit = dyntick_nohz_done &&
				     dyntick_irq_done &&
				     dyntick_nmi_done;	//\lnlbl{nmi_done1}
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
			shouldexit = dyntick_nohz_done &&
				     dyntick_irq_done &&
				     dyntick_nmi_done;	//\lnlbl{nmi_done2}
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
 * Macro that allows dyntick_irq() and dyntick_nmi() code to run atomically
 * with respect to dyntick_nohz(), but still allows dyntick_irq() and
 * dyntick_nmi() to be interleaved with other processes.
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irq-nmi-ssl:EXECUTE_MAINLINE,style=N,commandchars=\@\[\]]
#define EXECUTE_MAINLINE(label, stmt) \
label: skip; \
		atomic { \
			if \
			:: in_dyntick_irq || \
			   in_dyntick_nmi -> goto label; \
			:: else -> stmt; \
			fi; \
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

proctype dyntick_nohz()
{
	byte tmp;
	byte i = 0;
	bit old_gp_idle;

	do
	:: i >= MAX_DYNTICK_LOOP_NOHZ -> break;
	:: i < MAX_DYNTICK_LOOP_NOHZ ->

		/*
		 * The following corresponds to rcu_exit_nohz(), along
		 * with code to check for grace_period() jumping the gun.
		 */

		EXECUTE_MAINLINE(stmt1, tmp = dynticks_progress_counter)
		EXECUTE_MAINLINE(stmt2, dynticks_progress_counter = tmp + 1; old_gp_idle = (grace_period_state == GP_IDLE); assert((dynticks_progress_counter & 1) == 1))

		/*
		 * The following corresponds to rcu_enter_nohz(), along
		 * with code to check for grace_period() jumping the gun.
		 */

		EXECUTE_MAINLINE(stmt3, tmp = dynticks_progress_counter; assert(!old_gp_idle || grace_period_state != GP_DONE))
		EXECUTE_MAINLINE(stmt4, dynticks_progress_counter = tmp + 1; assert((dynticks_progress_counter & 1) == 0))
		i++;
	od;
	dyntick_nohz_done = 1;
}

/*
 * Macro that allows dyntick_nmi() code to run atomically with respect
 * to dyntick_irq(), but still allows dyntick_nmi() to be interleaved
 * with other processes.  This macro must be used when accessing
 * external state, but statements that access state that is purely
 * local to dyntick_irq() can be permitted to run in parallel with
 * dyntick_nmi().  In addition, global state that is shared only
 * with dyntick_nohz() may also be modified even when dyntick_nmi()
 * is running.
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irq-nmi-ssl:EXECUTE_IRQ,style=N,commandchars=\@\[\]]
#define EXECUTE_IRQ(label, stmt) \
label: skip; \
		atomic { \
			if \
			:: in_dyntick_nmi -> goto label; \
			:: else -> stmt; \
			fi; \
		}
//\end{snippet}

/*
 * Validation code corresponding to rcu_irq_enter() and rcu_irq_exit().
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irq-nmi-ssl:dyntick_irq,style=N,gobbleblank=yes,commandchars=\@\[\]]
proctype dyntick_irq()
{
	byte tmp;
	byte i = 0;
	byte j = 0;
	bit old_gp_idle;
	bit outermost;
								//\fcvblank
	do
	:: i >= MAX_DYNTICK_LOOP_IRQ &&
	   j >= MAX_DYNTICK_LOOP_IRQ -> break;
	:: i < MAX_DYNTICK_LOOP_IRQ ->

		/* Tell dyntick_nohz() that we are in interrupt handler. */

		atomic {
			outermost = (in_dyntick_irq == 0);
			in_dyntick_irq = 1;
		}

		/* Validation code corresponding to rcu_irq_enter(). */

stmt1: skip;				//\lnlbl{stmt1:b}
		atomic {
			if
			:: in_dyntick_nmi -> goto stmt1;
			:: !in_dyntick_nmi && rcu_update_flag ->
				goto stmt1_then;
			:: else -> goto stmt1_else;
			fi;
		}
stmt1_then: skip;
		EXECUTE_IRQ(stmt1_1, tmp = rcu_update_flag)
		EXECUTE_IRQ(stmt1_2, rcu_update_flag = tmp + 1)
stmt1_else: skip;			//\lnlbl{stmt1:e}
stmt2: skip;	atomic {
			if
			:: in_dyntick_nmi -> goto stmt2;
			:: !in_dyntick_nmi &&
			   !in_interrupt &&
			   (dynticks_progress_counter & 1) == 0 ->
			   	goto stmt2_then;
			:: else -> goto stmt2_else;
			fi;
		}
stmt2_then: skip;
		EXECUTE_IRQ(stmt2_1,
		            tmp = dynticks_progress_counter)
		EXECUTE_IRQ(stmt2_2,
		            dynticks_progress_counter = tmp + 1)
		EXECUTE_IRQ(stmt2_3, tmp = rcu_update_flag)
		EXECUTE_IRQ(stmt2_4, rcu_update_flag = tmp + 1)
stmt2_else: skip;

		/* 
		 * And a snippet from __irq_enter() corresponding to
		 * the add_preempt_count().
		 */

		EXECUTE_IRQ(stmt3, tmp = in_interrupt)
		EXECUTE_IRQ(stmt4, in_interrupt = tmp + 1)

		/* Capture state to see if grace_period() is behaving. */

stmt5: skip;
		atomic {
			if
			:: in_dyntick_nmi -> goto stmt4;
			:: !in_dyntick_nmi && outermost ->
				old_gp_idle = (grace_period_state == GP_IDLE);
			:: else -> skip;
			fi;
		}

		/* Count the entry for termination and nesting. */

		i++;			//\lnlbl{inc_i}

	/* Note that we cannot exit a handler we have not yet entered! */

	:: j < i ->

		/* See if we can catch grace_period() misbehaving. */

stmt6: skip;
		atomic {
			if
			:: in_dyntick_nmi -> goto stmt6;
			:: !in_dyntick_nmi && j + 1 == i ->
				assert(!old_gp_idle ||
				       grace_period_state != GP_DONE);
			:: else -> skip;
			fi;
		}

		/*
		 * Validation code corresponding to the sub_preempt_count()
		 * in __irq_exit().
		 */

		EXECUTE_IRQ(stmt7, tmp = in_interrupt);
		EXECUTE_IRQ(stmt8, in_interrupt = tmp - 1);

		/* Validation code corresponding to rcu_irq_exit(). */

stmt9: skip;
		atomic {
			if
			:: in_dyntick_nmi -> goto stmt9;
			:: !in_dyntick_nmi && rcu_update_flag != 0 ->
				goto stmt9_then;
			:: else -> goto stmt9_else;
			fi;
		}
stmt9_then: skip;
		EXECUTE_IRQ(stmt9_1, tmp = rcu_update_flag)
		EXECUTE_IRQ(stmt9_2, rcu_update_flag = tmp - 1)
stmt9_3: skip;
		atomic {
			if
			:: in_dyntick_nmi -> goto stmt9_3;
			:: !in_dyntick_nmi && rcu_update_flag == 0 ->
				goto stmt9_3_then;
			:: else -> goto stmt9_3_else;
			fi;
		}
stmt9_3_then: skip;
		EXECUTE_IRQ(stmt9_3_1,
		            tmp = dynticks_progress_counter)
		EXECUTE_IRQ(stmt9_3_2,
		            dynticks_progress_counter = tmp + 1)
stmt9_3_else:
stmt9_else: skip;

		/*
		 * Count the exit and let dyntick_nohz() know if we
		 * have completely exited a nested set of interrupts.
		 */

		atomic {
			j++;
			in_dyntick_irq = (i != j);
		}
	od;
	dyntick_irq_done = 1;
}
//\end{snippet}

/*
 * Validation code corresponding to rcu_irq_enter() and rcu_irq_exit().
 * Similar to dyntick_irq(), but done atomically.  This is a bit of
 * a cheat, since the code would not really be atomic with respect
 * to grace_period(), but one step at a time.
 */

//\begin{snippet}[labelbase=ln:formal:promela:dyntick:dyntickRCU-irq-nmi-ssl:dyntick_nmi,style=N,gobbleblank=yes,commandchars=\@\[\]]
proctype dyntick_nmi()
{
	byte tmp;
	byte i = 0;
	bit old_gp_idle;
								//\fcvblank
	do
	:: i >= MAX_DYNTICK_LOOP_NMI -> break;
	:: i < MAX_DYNTICK_LOOP_NMI ->

		/* Tell dyntick_nohz() that we are in interrupt handler. */

		in_dyntick_nmi = 1;

		/* Validation code corresponding to rcu_irq_enter(). */

		if
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
		fi;

		/* 
		 * And a snippet from __irq_enter() corresponding to
		 * the add_preempt_count().
		 */

		tmp = in_interrupt;
		in_interrupt = tmp + 1;

		/* Capture state to see if grace_period() is behaving. */

		old_gp_idle = (grace_period_state == GP_IDLE);

		/* See if we can catch grace_period() misbehaving. */

		assert(!old_gp_idle ||
		       grace_period_state != GP_DONE);

		/*
		 * Validation code corresponding to the sub_preempt_count()
		 * in __irq_exit().
		 */

		tmp = in_interrupt;
		in_interrupt = tmp - 1;

		/* Validation code corresponding to rcu_irq_exit(). */

		if
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
		fi;

		/*
		 * Count the exit and let dyntick_irq() and dyntick_nohz()
		 * know that we have exited the NMI.
		 */

		atomic {
			i++;
			in_dyntick_nmi = 0;
		}
	od;
	dyntick_nmi_done = 1;
}
//\end{snippet}

init {
	atomic {
		run dyntick_nohz();
		run dyntick_irq();
		run dyntick_nmi();
		run grace_period();
	}
}
