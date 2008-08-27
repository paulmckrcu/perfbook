#define THREAD_0 \
	do { \
		state.x = 1; \
		eieio(); \
		state.y = 1; \
		hwsync(); \
		state.d1 = 1; \
		hwsync(); \
	} while (0)

#define THREAD_1 \
	do { \
		/* cisync(&state.y, &state.a); */ \
		state.a = state.y; \
		cisync(state.a); \
		state.a1 = state.x; \
		hwsync(); \
		state.d = 1; \
		hwsync(); \
		while (state.d1 != 1) \
			barrier(); \
		hwsync(); \
		if (state.a == 1 &&  \
		    state.a1 == 0) { \
			state.badcount++; \
			break; \
		} \
	} while (0)

/* #define THREAD_2 \ */

/* #define THREAD_3 */

/* #define THREAD_4 */

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 1, &state.a },
	{ 1, &state.x },
	{ 0, &state.y },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0 /* 0 */, thread_0 },
	{ 1 /* 2 */, thread_1 },
	{-1, NULL },
};
