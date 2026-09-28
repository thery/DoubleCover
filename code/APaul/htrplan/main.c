// htrp EVAL x0 x1 m [-c]
// Runs the search of Program 2 on [x0, x1) at level m, with EVAL = mpfr
// (Program 1) or fix (Program 3).  Every candidate is then decided by
// check_mpfr, which is outside the superset.  With -c, every candidate is
// printed, so that two runs can be compared line by line.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "search.h"
#include "eval.h"

static unsigned long checks = 0, found = 0;
static int print_all = 0;

static void
report (double x, int m)
{
  checks ++;
  if (print_all) printf ("c %la\n", x);
  if (check_mpfr (x, m)) {
    printf ("%la\n", x);
    found ++;
  }
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
  if (strcmp (argv[1], "mpfr") == 0)
    search (eval_mpfr, expo_mpfr, report, x0, x1, m);
  else {
    fix_init ();
    search (eval_fix, expo_fix, report, x0, x1, m);
  }
  printf ("%lu checks, found %lu hard-to-round\n", checks, found);
  return 0;
}
