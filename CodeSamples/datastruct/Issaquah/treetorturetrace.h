/*
 * treetorturetrace.h: simple event tracing
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
 * Copyright (c) 2014-2019 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2019 Paul E. McKenney, Facebook.
 */

#ifndef _TREETORTURETRACE_H_
#define _TREETORTURETRACE_H_

#ifdef DEBUG_TRACE

struct trace_group;

static void tracing_enable(void);
static void tracing_disable(void);
#define trace(t, n, on) \
	_trace(t, n, on, __FILE__, __func__, __LINE__)
static void _trace(struct treeroot *t, struct treenode *tnp, char *on,
		   char *file, const char *const f, int ln);
static void trace_dump_thread(struct trace_group *tgp);

#else /* #ifdef DEBUG_TRACE */

static inline void tracing_init(int me)
{
}

static inline void tracing_enable(void)
{
}

static inline void tracing_disable(void)
{
}

#define trace(t, n, on) do { } while (0)

#endif /* #else #ifdef DEBUG_TRACE */

void trace_dump_all_threads(void);

static inline void trace_result(struct treeroot *trp,
				struct treenode *cur, int ret)
{
#ifdef DEBUG_TRACE
	char buf[32];

	sprintf(buf, "ERR%d", ret);
	trace(trp, cur, buf);
#endif /* #ifdef DEBUG_TRACE */
}

static inline void trace_move(struct treeroot *trp, int key, void *data,
			      char *s)
{
#ifdef DEBUG_TRACE
	struct treenode cur;

	cur.key = key;
	cur.data = data;
	cur.existence = NULL;
	trace(trp, &cur, s);
#endif /* #ifdef DEBUG_TRACE */
}

#endif /* #ifdef _TREETORTURETRACE_H_ */
