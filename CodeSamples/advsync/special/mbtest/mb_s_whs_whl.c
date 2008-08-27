#define THREAD_0 \
	do { \
		state.a = 1; \
	} while (0)

#define THREAD_1 \
	do { \
		while (state.a == 0) \
			continue; \
		hwsync(); \
		state.b = 1; \
	} while (0)

#define THREAD_2 \
	do { \
		while (state.b == 0) \
			continue; \
		hwsync(); \
		if (state.a == 0) \
			state.badcount++; \
		break; \
	} while (0)

/* #define THREAD_3 */
/* #define THREAD_4 */

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 0, &state.b },
	{ 2, &state.a },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0, thread_0 },
	{ 1, thread_1 },
	{ 2, thread_2 },
	{-1, NULL },
};
