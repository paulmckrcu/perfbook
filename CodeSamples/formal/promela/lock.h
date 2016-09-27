#define spin_lock(mutex) \
	do \
	:: 1 -> atomic { \
			if \
			:: mutex == 0 -> \
				mutex = 1; \
				break \
			:: else -> skip \
			fi \
		} \
	od

#define spin_unlock(mutex) \
	mutex = 0
