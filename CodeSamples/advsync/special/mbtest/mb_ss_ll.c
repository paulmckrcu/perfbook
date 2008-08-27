#define THREAD_0 \
	do { \
		state.a = 1; \
		state.b = 1; \
	} while (0)

#define THREAD_1 \
	do { \
		state.y = state.b; \
		state.x = state.a; \
		if (state.y == 1 && state.x == 0) { \
			state.badcount++; \
			break; \
		} \
	} while (state.f > 1)

/* #define THREAD_2 */
/* #define THREAD_3 */
/* #define THREAD_4 */

#include "mbtest.h"

struct cache_preload cache_preload[] = {
	{ 0, &state.b },
	{ 1, &state.a },
	{ 1, &state.x },
	{ 1, &state.y },
	{-1, NULL },
};

struct thread_assignment thread_assignment[] = {
	{ 0, thread_0 },
	{ 1, thread_1 },
	{-1, NULL },
};
