/*
 * hashtorture.h: simple user-level performance/stress test of hash tables.
 *
 * Usage:
 *
 *	@@@
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2013 Paul E. McKenney, IBM Corporation.
 */

/*
 * Test variables.
 */

struct testhe {
	struct ht_elem the_e;
	unsigned long data;
};

int testcmp(struct ht_elem *htep, void *key)
{
	struct testhe *thep;

	thep = container_of(htep, struct testhe, the_e);
	return ((unsigned long)key) == thep->data;
}

void smoketest(void)
{
	struct testhe e1 = { .data = 1 };
	struct testhe e2 = { .data = 2 };
	struct testhe e3 = { .data = 3 };
	struct testhe e4 = { .data = 4 };
	struct hashtab *htp;
	int i;

	htp = hashtab_alloc(5);
	BUG_ON(htp == NULL);

	/* Should be empty. */
	for (i = 1; i <= 4; i++) {
		hashtab_lock_lookup(htp, i);
		BUG_ON(hashtab_lookup(htp, (unsigned long)i, (void *)i,
				      testcmp));
		hashtab_unlock_lookup(htp, i);
	}

	/* Add one by one and check. */
	hashtab_lock_mod(htp, 1);
	hashtab_add(htp, 1, &e1.the_e);
	BUG_ON(!hashtab_lookup(htp, 1, (void *)1, testcmp));
	hashtab_unlock_mod(htp, 1);
	hashtab_lock_mod(htp, 2);
	hashtab_add(htp, 2, &e2.the_e);
	BUG_ON(!hashtab_lookup(htp, 2, (void *)2, testcmp));
	hashtab_unlock_mod(htp, 2);
	hashtab_lock_mod(htp, 3);
	hashtab_add(htp, 3, &e3.the_e);
	BUG_ON(!hashtab_lookup(htp, 3, (void *)3, testcmp));
	hashtab_unlock_mod(htp, 3);
	hashtab_lock_mod(htp, 4);
	hashtab_add(htp, 4, &e4.the_e);
	BUG_ON(!hashtab_lookup(htp, 4, (void *)4, testcmp));
	hashtab_unlock_mod(htp, 4);

	/* Should be full. */
	for (i = 1; i <= 4; i++) {
		hashtab_lock_lookup(htp, i);
		BUG_ON(!hashtab_lookup(htp, (unsigned long)i, (void *)i,
				       testcmp));
		hashtab_unlock_lookup(htp, i);
	}

	/* Delete all and check one by one. */
	hashtab_lock_mod(htp, 1);
	hashtab_del(&e1.the_e);
	BUG_ON(hashtab_lookup(htp, 1, (void *)1, testcmp));
	hashtab_unlock_mod(htp, 1);
	hashtab_lock_mod(htp, 2);
	hashtab_del(&e2.the_e);
	BUG_ON(hashtab_lookup(htp, 2, (void *)2, testcmp));
	hashtab_unlock_mod(htp, 2);
	hashtab_lock_mod(htp, 3);
	hashtab_del(&e3.the_e);
	BUG_ON(hashtab_lookup(htp, 3, (void *)3, testcmp));
	hashtab_unlock_mod(htp, 3);
	hashtab_lock_mod(htp, 4);
	hashtab_del(&e4.the_e);
	BUG_ON(hashtab_lookup(htp, 4, (void *)4, testcmp));
	hashtab_unlock_mod(htp, 4);

	/* Should be empty. */
	for (i = 1; i <= 4; i++) {
		hashtab_lock_lookup(htp, i);
		BUG_ON(hashtab_lookup(htp, (unsigned long)i, (void *)i,
				      testcmp));
		hashtab_unlock_lookup(htp, i);
	}
}

/*
 * Mainprogram.
 */
void usage(int argc, char *argv[])
{
	fprintf(stderr, "Usage: %s --smoketest\n", argv[0]);
	exit(-1);
}

int main(int argc, char *argv[])
{
	int i = 1;

	smp_init();

	while (i < argc) {
		if (strcmp(argv[i], "--smoketest") == 0)
			smoketest();
		else
			usage(argc, argv);
		i++;
	}
}
