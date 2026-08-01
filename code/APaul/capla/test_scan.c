/* test_scan.c -- driver for scan.b.
 *
 * Runs the same inner loop in plain C (the reference, copied from
 * htr_plain.c) and through the Capla function, and compares.  Capla has
 * no I/O, so the printing has to live here.
 */

#include <stdint.h>
#include <stdio.h>
#include <time.h>

extern uint64_t scan_count (uint64_t a, uint64_t b, uint64_t twoE,
                            uint64_t n);
extern void scan_last (uint64_t a, uint64_t b, uint64_t twoE, uint64_t n,
                       uint64_t *res);

/* the reference: htr_plain.c's inner loop.  Written like scan_last, one
 * pass returning both the count and the final A, so the two sides do the
 * same amount of work and their times can be compared. */
static void ref_last (uint64_t a, uint64_t b, uint64_t twoE, uint64_t n,
                      uint64_t *res)
{
  uint64_t cnt = 0, x = a, i;
  for (i = 0; i < n; i++)
    {
      if (x < twoE)
        cnt++;
      x = x + b;
    }
  res[0] = cnt;
  res[1] = x;
}

#define LOG2N   20                    /* chunk size n = 2^LOG2N, as in htr  */
#define MHRC    35                    /* identical bits after the round bit */
#define NCHUNK  200                   /* chunks to run                      */

/* The real search has E = (n^2/2)|phi''| + 2^(64-MHRC); over the interval
 * the first term is close to 2^48.4, which is the value used here.  With
 * twoE = 2E, a chunk of 2^LOG2N points is expected to hold about
 * n * twoE / 2^64 ~ 41 candidates -- the density htr_plain.c reports. */
#define EBASE   ((uint64_t) 442721857769029ULL)        /* ~ 2^48.653        */

int main (void)
{
  const uint64_t n = ((uint64_t) 1) << LOG2N;
  const uint64_t twoE = 2 * (EBASE + (((uint64_t) 1) << (64 - MHRC)));
  uint64_t a = 88172645463325252ULL;  /* an arbitrary start for the walk    */
  uint64_t total_c = 0, total_b = 0;
  double t_c, t_b;
  clock_t t0;
  uint64_t res[2];
  int k, bad = 0;

  /* Same (a, b) sequence fed to both, so the counts must agree exactly.
   * b is kept odd and large, as the real B = frac(exp x / 2) * 2^64 is. */
  t0 = clock ();
  {
    uint64_t x = a;
    for (k = 0; k < NCHUNK; k++)
      {
        uint64_t b = 11400714819323198485ULL * (uint64_t) (k + 1) | 1;
        ref_last (x, b, twoE, n, res);
        total_c += res[0];
        x = res[1];
      }
  }
  t_c = (double) (clock () - t0) / CLOCKS_PER_SEC;

  t0 = clock ();
  {
    uint64_t x = a;
    for (k = 0; k < NCHUNK; k++)
      {
        uint64_t b = 11400714819323198485ULL * (uint64_t) (k + 1) | 1;
        scan_last (x, b, twoE, n, res);
        total_b += res[0];
        x = res[1];
      }
  }
  t_b = (double) (clock () - t0) / CLOCKS_PER_SEC;

  /* spot-check scan_count against scan_last on the first chunk */
  {
    uint64_t b = 11400714819323198485ULL | 1;
    uint64_t c1 = scan_count (a, b, twoE, n);
    scan_last (a, b, twoE, n, res);
    if (c1 != res[0])
      {
        printf ("scan_count %llu != scan_last %llu\n",
                (unsigned long long) c1, (unsigned long long) res[0]);
        bad = 1;
      }
  }

  if (total_c != total_b)
    bad = 1;

  printf ("%d chunks of 2^%d, twoE = %llu\n", NCHUNK, LOG2N,
          (unsigned long long) twoE);
  printf ("  C     %llu candidates in %.3f s\n",
          (unsigned long long) total_c, t_c);
  printf ("  Capla %llu candidates in %.3f s\n",
          (unsigned long long) total_b, t_b);
  printf ("  %.1f candidates per chunk\n", (double) total_c / NCHUNK);
  printf (bad ? "MISMATCH\n" : "counts agree\n");
  return bad;
}
