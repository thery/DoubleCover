// htrp EVAL x0 x1 m [-c]
// Runs Program 2, the generic search, on [x0, x1) at level m, with
// EVAL = mpfr (the initial program's evaluators) or fix (Program 3, the
// proved evaluator).  Every candidate comes with the verdict of Program
// 2's check; an undecided one is printed with a "u" and kept.  With -c, every candidate
// is printed, so that two runs can be compared line by line.
// Built without WITH_MPFR (the binary htr3), only EVAL = fix exists and
// the program is linked without MPFR.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "search.h"
#include "eval.h"

static unsigned long checks = 0, found = 0;
static int print_all = 0;

static void
report (double x, int m, int r)
{
  (void) m;
  checks ++;
  if (print_all) printf ("c %la\n", x);
  if (r == 1) {
    printf ("%la\n", x);
    found ++;
  }
  else if (r == 2)
    printf ("u %la\n", x);
}

int
main (int argc, char *argv[])
{
  if (argc < 5) {
    fprintf (stderr, "usage: htrp mpfr|fix x0 x1 m [-c]\n");
    return 1;
  }
  double x0 = strtod (argv[2], NULL), x1 = strtod (argv[3], NULL);
  int m = atoi (argv[4]);
  print_all = argc > 5 && strcmp (argv[5], "-c") == 0;
#ifdef WITH_MPFR
  if (strcmp (argv[1], "mpfr") == 0) {
    search (eval_mpfr, low_mpfr, eval_mpfr, report, x0, x1, m);
  }
  else
#endif
  {
    fix_init ();
    search (eval_fix, low_fix, eval_fix, report, x0, x1, m);
  }
  printf ("%lu checks, found %lu hard-to-round\n", checks, found);
  return 0;
}
