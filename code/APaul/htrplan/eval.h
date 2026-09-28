// The evaluators that can be given to search.

#include <math.h>

// the initial program: MPFR, trusted
int expo_mpfr (double x);
void eval_mpfr (double *h, double *l, double *s, double x);
int check_mpfr (double x, int m);

// Program 3, the proved evaluator: integers only, to be proved
void fix_init (void);
int expo_fix (double x);
void eval_fix (double *h, double *l, double *s, double x);
int check_fix (double x, int m);
