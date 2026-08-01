/* test_htr.c -- driver for htr.b.
 *
 * Two modes, matching the two top-level interfaces htr.b offers.
 *
 *   test_htr [x0 x1]   the search: Capla fills an array with the hard
 *                      cases it finds.  Prints exactly what htr_plain.c
 *                      prints, so the outputs can be diffed.  Without
 *                      arguments it runs the whole interval, a couple of
 *                      minutes; with two it runs [x0, x1) instead.
 *
 *   test_htr -check    the checker: an oracle supplies the hard cases and
 *                      Capla only verifies that the search finds exactly
 *                      those.  A negative test follows, on a slice where
 *                      the oracle claims a case that is not there.
 *
 * The search itself is entirely in Capla; this only supplies the arrays
 * and does the printing Capla cannot do.
 */

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define X0NUM  4503599627370496LL          /* 0.25                          */
#define X1NUM  4503779771355591LL          /* 0.25001, as a double          */
#define NL     21                          /* limbs of 32 bits              */
#define MAXOUT 64                          /* room for the cases found      */

/* Capla's [[u32; n]; 8] is an array of row pointers, uint32_t**, and it
 * cannot allocate one itself, so the coefficient table is supplied here
 * and filled by init_coeffs inside the two entry points. */
extern uint64_t htr_search (int64_t x0, int64_t x1, uint32_t **CO,
                            int64_t *out, uint64_t cap, uint64_t *stats,
                            uint64_t n);
extern uint8_t htr_check (int64_t x0, int64_t x1, uint32_t **CO,
                          const int64_t *want, uint64_t k, uint64_t *stats,
                          uint64_t n);

/* The five hard-to-round cases, as BaCSeL and htr.c report them.  With
 * x = X / 2^54 and exp x in [1, 2), X is 2^52 plus the mantissa field. */
static const int64_t oracle[5] = {
  X0NUM + 0x2385331beLL,               /* 0x1.00002385331bep-2 */
  X0NUM + 0x561fc7e06LL,               /* 0x1.0000561fc7e06p-2 */
  X0NUM + 0x1cd08ef3d4LL,              /* 0x1.0001cd08ef3d4p-2 */
  X0NUM + 0x26c769e211LL,              /* 0x1.00026c769e211p-2 */
  X0NUM + 0x28a78a7303LL               /* 0x1.00028a78a7303p-2 */
};

static void fill_rows (uint32_t CO[8][NL], uint32_t *COp[8])
{
  int i;
  for (i = 0; i < 8; i++)
    COp[i] = CO[i];
}

int main (int argc, char **argv)
{
  uint32_t CO[8][NL];
  uint32_t *COp[8];
  uint64_t stats[2];

  fill_rows (CO, COp);

  if (argc == 2 && strcmp (argv[1], "-check") == 0)
    {
      int64_t bogus[1];
      uint8_t ok, bad;

      ok = htr_check (X0NUM, X1NUM, COp, oracle, 5, stats, NL);
      printf ("check against the 5 known cases: %s\n",
              ok ? "accepted" : "REJECTED");
      printf ("  %llu candidates, %llu hard-to-round\n",
              (unsigned long long) stats[0], (unsigned long long) stats[1]);

      /* negative test: on the first ten chunks there is no hard case, so
       * an oracle claiming one must be rejected */
      bogus[0] = X0NUM + 1;
      bad = htr_check (X0NUM, X0NUM + 10 * (1LL << 20), COp, bogus, 1,
                       stats, NL);
      printf ("check against a wrong oracle: %s\n",
              bad ? "ACCEPTED (wrong)" : "rejected");

      return (ok && !bad) ? 0 : 1;
    }

  {
    int64_t out[MAXOUT];
    int64_t x0 = X0NUM, x1 = X1NUM;
    uint64_t found, i;

    if (argc == 3)
      {
        x0 = strtoll (argv[1], NULL, 10);
        x1 = strtoll (argv[2], NULL, 10);
      }

    found = htr_search (x0, x1, COp, out, MAXOUT, stats, NL);

    for (i = 0; i < found && i < MAXOUT; i++)
      printf ("%lld/2^54\n", (long long) out[i]);
    if (found > MAXOUT)
      printf ("(%llu more, out array holds %d)\n",
              (unsigned long long) (found - MAXOUT), MAXOUT);

    printf ("%llu candidates, found %llu hard-to-round\n",
            (unsigned long long) stats[0], (unsigned long long) stats[1]);
  }
  return 0;
}
