// htrp EVAL x0 x1 m [-c]
// Runs Program 2, the generic search, on [x0, x1) at level m, with
// EVAL = mpfr (the initial program's evaluators) or fix (Program 3, the
// proved evaluator).  Prints the hard cases found, and the undecided ones
// with a "u".  With -c, it also prints every candidate, so that two runs
// can be compared line by line.
// Built without WITH_MPFR (the binary htr3), only EVAL = fix exists and
// the program is linked without MPFR.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "search.h"
#include "eval.h"

int
main (int argc, char *argv[])
{
  if (argc < 5) {
    fprintf (stderr, "usage: htrp mpfr|fix x0 x1 m [-c]\n");
    return 1;
  }
  double x0 = strtod (argv[2], NULL), x1 = strtod (argv[3], NULL);
  int m = atoi (argv[4]);
  int print_all = argc > 5 && strcmp (argv[5], "-c") == 0;
  // the array: 64 candidates a chunk to start with, then as many as
  // search says there are
  unsigned long cap = (unsigned long) ((x1 - x0) / (x0 > 0 ? x0 : -x0)
                                       * 0x1p53 / 0x1p20 + 1) * 64;
  struct cand *a = malloc (cap * sizeof (struct cand));
  unsigned long n;
  for (;;) {
#ifdef WITH_MPFR
    if (strcmp (argv[1], "mpfr") == 0)
      n = search (eval_mpfr, low_mpfr, check_mpfr, x0, x1, m, a, cap);
    else
#endif
    {
      fix_init ();
      n = search (eval_fix, low_fix, eval_fix, x0, x1, m, a, cap);
    }
    if (n <= cap) break;
    cap = n;
    a = realloc (a, cap * sizeof (struct cand));
  }
  unsigned long found = 0;
  for (unsigned long i = 0; i < n; i++) {
    if (print_all) printf ("c %la\n", a[i].x);
    if (a[i].v == 1) {
      printf ("%la\n", a[i].x);
      found ++;
    }
    else if (a[i].v == 2)
      printf ("u %la\n", a[i].x);
  }
  printf ("%lu checks, found %lu hard-to-round\n", n, found);
  free (a);
  return 0;
}
