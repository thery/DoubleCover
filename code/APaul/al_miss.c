// al_miss.c -- demonstrates that al.c's linear filter (n = 2^20) can MISS a
// genuine hard-to-round case of exp when it falls at a large index within a
// chunk.  All of al.c's filter/derivative code is used verbatim (dd_exp,
// get_uint64, the per-chunk A/B/E setup and the A += B inner loop).
//
// The documented worst case  x_a = 0x1.00006b1501522p-2  (exp(x_a) is within
// ~2^-30.8 of a machine number) is placed at index i0 = 2^19 of a single
// chunk  [x0, x0 + n*ux)  with  x0 = x_a - i0*ux.  In al.c's real run this
// same case is found because it happens to sit at index 5410 (< ~2^13); here
// it sits at 2^19, where the second-order drift of the linear model
// (~2^46 >> E = 2^34) throws A far outside the window, so check() is never
// called on it.
//
// Root cause: over a chunk the linear model's error is (n^2/2)*|phi''| with
// phi = exp*2^53; that reaches ~2^-15.6 (= ~2^48 in the 2^64 A-scale) for
// n = 2^20, far above the window E.  al.c's Taylor term (uint64)ldexp(dd,64)
// uses dd = exp*ux^2*n^2/2 (an *exp-value* remainder) and rounds to 0 -- it is
// under-scaled by 2^53 relative to the phase.  Soundness needs
// (n^2/2)*|phi''| <= E, i.e. n <= ~2^13 here (cf. Lefevre RR-4044, which uses
// 2^15/2^13-point subintervals, not 2^20).
//
//   gcc -O3 -march=native -std=c11 al_miss.c -o al_miss -lmpfr -lgmp -lm
#include <stdio.h>
#include <stdint.h>
#include <mpfr.h>
#include <math.h>
#include <assert.h>

// ---- verbatim from al.c ----
double ref_exp (double x){
  mpfr_t y; mpfr_exp_t emin = mpfr_get_emin();
  mpfr_set_emin(-1073); mpfr_init2(y,53); mpfr_set_d(y,x,MPFR_RNDN);
  int inex = mpfr_exp(y,y,MPFR_RNDZ); mpfr_subnormalize(y,inex,MPFR_RNDZ);
  double ret = mpfr_get_d(y,MPFR_RNDN); mpfr_clear(y); mpfr_set_emin(emin);
  return ret;
}
static void dd_exp (double *h, double *l, double *s, double x){
  mpfr_t t; mpfr_init2(t,3*53+2); mpfr_set_d(t,x,MPFR_RNDN); mpfr_exp(t,t,MPFR_RNDN);
  *h=mpfr_get_d(t,MPFR_RNDN); mpfr_sub_d(t,t,*h,MPFR_RNDN);
  *l=mpfr_get_d(t,MPFR_RNDN); mpfr_sub_d(t,t,*l,MPFR_RNDN);
  *s=mpfr_get_d(t,MPFR_RNDN); mpfr_clear(t);
}
unsigned long checks=0, found=0;
static int check (double x, int m){   // al.c's check(), returns 1 iff hard-to-round
  checks++; mpfr_t y,z; mpfr_init2(y,54); mpfr_init2(z,53+m);
  mpfr_set_d(y,x,MPFR_RNDN); mpfr_exp(z,y,MPFR_RNDN); mpfr_set(y,z,MPFR_RNDN);
  int hard = (mpfr_cmp(y,z)==0); if (hard) found++;
  mpfr_clear(y); mpfr_clear(z); return hard;
}
static uint64_t get_uint64 (double x){
  assert(-1 < x && x < 1); x = ldexp(x,64);
  if (x >= 0) return x; uint64_t ret = (uint64_t)(-x); return ~ret + (uint64_t)1;
}

int main(){
  int m = 30;
  long long HARD_M = 4503628371989794LL;   // x_a = HARD_M / 2^54 = 0x1.00006b1501522p-2
  double x_a = ldexp((double)HARD_M, -54);
  uint64_t n = 1ul << 20;
  uint64_t i0 = 1ul << 19;                  // put x_a at index 2^19 of the chunk
  double x0 = ldexp((double)(HARD_M - (long long)i0), -54);   // chunk start

  // --- (1) x_a really is a hard-to-round case ---
  int hard = check(x_a, m);
  printf("(1) direct check of x_a = %a : %s\n", x_a, hard ? "HARD-TO-ROUND" : "not hard");
  printf("    (x0 + i0*ux == x_a ? %s)\n\n",
         (x0 + (double)i0 * ldexp(1.0, -54) == x_a) ? "yes" : "NO");
  found = 0; // reset: count only what the filter finds

  // --- (2) run al.c's filter on the single chunk [x0, x0 + n*ux) ---
  int e, e0; frexp(x0, &e0);
  double ux = ldexp(1.0, e0 - 53);          // ulp(x0) = 2^-54
  double y0 = ref_exp(x0); frexp(y0, &e);   // exp binade
  double h, l, s, x = x0;
  dd_exp(&h,&l,&s,x);
  double dh = h*ux, dl = l*ux, dd = h*ux*ux;
  h = ldexp(h,54-e); l = ldexp(l,54-e);
  if (l >= 1.0) l -= 1.0; while (l < 0) l += 1.0;
  s = ldexp(s,54-e);
  uint64_t lu = get_uint64(l), su = get_uint64(s), A = lu + su;
  dh = ldexp(dh,54-e); dl = ldexp(dl,54-e);
  uint64_t B = get_uint64(dh) + get_uint64(dl);
  dd = dd/2.0*n*n;
  uint64_t E = (uint64_t) ldexp(dd,64) + (1ul << (64-m));
  A += E;
  uint64_t A_at_i0 = 0; int flagged_i0 = 0;
  for (uint64_t i = 0; i < n; i++){
    if (i == i0){ A_at_i0 = A; flagged_i0 = (A < 2*E); }
    if (A < 2*E){ double xi = x + i*ux; check(xi, m); }
    A += B;
  }
  printf("(2) al.c filter over the chunk holding x_a at i0 = 2^19:\n");
  printf("    E = %lu (2^%.0f),  window 2E = %lu\n", E, log2((double)E), 2*E);
  printf("    Taylor term (uint64)ldexp(dd,64) = %lu   [rounds to 0]\n",
         (uint64_t) ldexp(dd,64));
  printf("    A at i0 = %lu  (= 2^%.1f)   <  2E ?  %s\n",
         A_at_i0, log2((double)A_at_i0), flagged_i0 ? "yes" : "NO");
  printf("    => check() called on x_a ? %s\n", flagged_i0 ? "yes" : "NO");
  printf("    => hard cases the filter FOUND in this chunk: %lu\n\n", found);

  printf(found == 0
    ? "RESULT: the filter MISSES the hard case x_a (found = 0), although it is\n"
      "        genuinely hard and lies exactly on the grid of the chunk.\n"
    : "RESULT: (unexpected) the filter found %lu hard case(s).\n", found);
  return 0;
}
