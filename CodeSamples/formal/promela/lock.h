//\begin{snippet}[labelbase=ln:formal:promela:lock:whole,commandchars=\!\[\]]
#define spin_lock(mutex) \
	do /* \lnlbl{dood:b} */\
	:: 1 -> atomic { /* \lnlbl{one} */\
			if \
			:: mutex == 0 -> /* \lnlbl{notheld} */\
				mutex = 1; /* \lnlbl{acq} */\
				break /* \lnlbl{break} */\
			:: else -> skip /* \lnlbl{held} */\
			fi \
		} \
	od /* \lnlbl{dood:e} */

#define spin_unlock(mutex) \
	mutex = 0
//\end{snippet}
