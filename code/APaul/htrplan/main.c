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
  struct cands c;
#ifdef WITH_MPFR
  if (strcmp (argv[1], "mpfr") == 0)
    c = search (eval_mpfr, low_mpfr, eval_mpfr, x0, x1, m);
  else
#endif
  {
    fix_init ();
    c = search (eval_fix, low_fix, eval_fix, x0, x1, m);
  }
  unsigned long found = 0;
  for (unsigned long i = 0; i < c.n; i++) {
    if (print_all) printf ("c %la\n", c.a[i].x);
    if (c.a[i].v == 1) {
      printf ("%la\n", c.a[i].x);
      found ++;
    }
    else if (c.a[i].v == 2)
      printf ("u %la\n", c.a[i].x);
  }
  printf ("%lu checks, found %lu hard-to-round\n", c.n, found);
  free (c.a);
  return 0;
}
