/* htr_plain.c -- the whole hard-to-round search for exp on [0.25, 0.25001),
 * self-contained, in plain C.
 *
 * Same result as htr.c (five cases with m = 35), but with none of its
 * machinery: no MPFR, no floating point, no ldexp/frexp/nextafter, no
 * library call other than printf.  What is left is
 *
 *   - a fixed-width integer type (arrays of 32-bit limbs held in uint32_t,
 *     products taken in uint64_t, so no 128-bit type is needed),
 *   - the certified degree-7 polynomial of rocq/Cheb.v, evaluated exactly,
 *   - the Lefevre scan, on uint64_t,
 *   - a screening test that is three bit comparisons.
 *
 * ---------------------------------------------------------------- the maths
 *
 * P is the degree-7 Chebyshev interpolant of exp on [0.25, 0.25001),
 *   P(x) = (sum_{k=0}^{7} A_k (x - c)^k) / 2^cden,   c = Cc / 2^xden,
 * certified in Rocq (Cheb.cheb_valid) to satisfy |exp x - P x| <= 2^-160
 * over the whole interval.  Since the search only ever asks questions at the
 * 2^-88 level, P may replace exp everywhere below.
 *
 * With x = X / 2^54 and d = X - Cc, the integer
 *   V = P(x) * 2^vden,   vden = cden + 7*xden = 598
 * is exact, and it is what poly_eval computes (Horner, at most 599 bits).
 * Everything else is reading bits out of V:
 *
 *   bit 597 of V is the leading bit of exp x (exp x lies in [1,2)),
 *   so the binary64 round bit sits at bit Pbits = vden - 53 = 545, and
 *   V mod 2^545 is the distance to the round-bit grid.
 *
 *   B    = bits [535, 599) of V         = frac(exp x / 2) * 2^64
 *   E    = (V >> 550) + 2^(64-m)        = (n^2/2)|phi''| + 2^(64-m)
 *   A    = bits [481, 545) of V  +  E
 *
 * The 550 is vden - ddexp - 64 with ddexp = 2*(e_x - 53) + (54 - e_y) - 1
 * + 2*log2N = -16: the second derivative of exp is exp itself, scaled by
 * ux^2 = 2^(2*(e_x-53)), put in the phase scale by 2^(54-e_y), halved, and
 * multiplied by n^2.  (al.c omitted the 2^(54-e_y) factor, so its E was
 * 2^34 instead of ~2^48.4 and its filter could step over a genuine case;
 * htr.c added it back, and that is what the "+ (V >> 550)" is here.)
 *
 * A hard-to-round case is a point whose distance to the grid is below
 * 2^(545-35), i.e. min(r, 2^545 - r) < 2^510 with r = V mod 2^545.  Writing
 * r = top*2^510 + low with top on 35 bits, that is simply
 *      top == 0,   or   top == 2^35-1 and low != 0
 * -- "the 35 bits after the round bit are all equal".  No division needed.
 *
 * Expected output (equal to htr.c's, and to BaCSeL's):
 *   0x1.00002385331bep-2  0x1.0000561fc7e06p-2  0x1.0001cd08ef3d4p-2
 *   0x1.00026c769e211p-2  0x1.00028a78a7303p-2
 */

#include <stdint.h>
#include <stdio.h>

/* ------------------------------------------------------------ parameters */

#define XDEN     54           /* grid scale: x = X / 2^XDEN                 */
#define CDEN    220           /* coefficient denominator                    */
#define VDEN    (CDEN + 7 * XDEN)          /* = 598, scale of V             */
#define PBITS   (VDEN - 53)                /* = 545, the round-bit position */
#define MHRC     35           /* identical bits required after the round bit */
#define LOG2N    20           /* chunk size n = 2^LOG2N                     */
#define DDEXP   (2 * (-1 - 53) + (54 - 1) - 1 + 2 * LOG2N)      /* = -16    */
#define ESHIFT  (VDEN - DDEXP - 64)        /* = 550                         */
#define ASHIFT  (PBITS - 64)               /* = 481                         */
#define BSHIFT  (VDEN + 1 - 64)            /* = 535                         */
#define TOPBIT  (PBITS - MHRC)             /* = 510                         */

#define X0NUM  4503599627370496LL          /* 0.25                          */
#define X1NUM  4503779771355591LL          /* 0.25001, as a double          */
#define CCNUM  4503689699363044LL          /* expansion centre c * 2^XDEN   */

/* --------------------------------------------------- fixed-width integers */

/* A value is 21 limbs of 32 bits, i.e. an integer modulo 2^672, in two's
 * complement, least significant limb first.  Every quantity below fits:
 * the largest is V < 2^599, and the Horner intermediates never exceed it. */
#define NL 21

static void big_set (uint32_t *r, const uint32_t *a)
{
  int i;
  for (i = 0; i < NL; i++)
    r[i] = a[i];
}

static void big_add (uint32_t *r, const uint32_t *a)
{
  uint64_t carry = 0;
  int i;
  for (i = 0; i < NL; i++)
    {
      uint64_t t = (uint64_t) r[i] + (uint64_t) a[i] + carry;
      r[i] = (uint32_t) t;
      carry = t >> 32;
    }
}

static void big_mul32 (uint32_t *r, uint32_t m)
{
  uint64_t carry = 0;
  int i;
  for (i = 0; i < NL; i++)
    {
      uint64_t t = (uint64_t) r[i] * (uint64_t) m + carry;
      r[i] = (uint32_t) t;
      carry = t >> 32;
    }
}

/* r <<= 32 (one limb) */
static void big_shl_limb (uint32_t *r)
{
  int i;
  for (i = NL - 1; i > 0; i--)
    r[i] = r[i - 1];
  r[0] = 0;
}

/* r <<= n, for 0 <= n */
static void big_shl (uint32_t *r, int n)
{
  int limbs = n / 32;
  int bits = n % 32;
  int i;
  for (i = NL - 1; i >= 0; i--)
    r[i] = (i - limbs >= 0) ? r[i - limbs] : 0;
  if (bits > 0)
    for (i = NL - 1; i >= 0; i--)
      {
        uint32_t lo = (i > 0) ? (r[i - 1] >> (32 - bits)) : 0;
        r[i] = (r[i] << bits) | lo;
      }
}

/* r = -r */
static void big_neg (uint32_t *r)
{
  uint64_t carry = 1;
  int i;
  for (i = 0; i < NL; i++)
    {
      uint64_t t = (uint64_t) (~r[i]) + carry;
      r[i] = (uint32_t) t;
      carry = t >> 32;
    }
}

/* the 64 bits of a starting at bit p (p + 64 <= 32*NL) */
static uint64_t big_bits64 (const uint32_t *a, int p)
{
  int limb = p / 32;
  int bits = p % 32;
  uint64_t lo = (uint64_t) a[limb] | ((uint64_t) a[limb + 1] << 32);
  if (bits == 0)
    return lo;
  return (lo >> bits) | ((uint64_t) a[limb + 2] << (64 - bits));
}

/* is any bit of a below position p set? */
static int big_low_nonzero (const uint32_t *a, int p)
{
  int limb = p / 32;
  int bits = p % 32;
  int i;
  for (i = 0; i < limb; i++)
    if (a[i] != 0)
      return 1;
  if (bits > 0 && (a[limb] & (((uint32_t) 1 << bits) - 1)) != 0)
    return 1;
  return 0;
}

/* ----------------------------------------- the certified polynomial (Cheb) */

static const uint32_t A0[NL] = { 0xbfcd8b33U, 0xa2766a2aU, 0x1fa1f522U, 0xd9c95d93U, 0x80be2eebU, 0xa361f790U, 0x148b64f7U };
static const uint32_t A1[NL] = { 0xceaedbbcU, 0xa47b8f34U, 0x1fa1f522U, 0xd9c95d93U, 0x80be2eebU, 0xa361f790U, 0x148b64f7U };
static const uint32_t A2[NL] = { 0x15ac5fd8U, 0x4593777aU, 0x351b3ee6U, 0xece4aeccU, 0x405f1775U, 0xd1b0fbc8U, 0x0a45b27bU };
static const uint32_t A3[NL] = { 0x02965a86U, 0xe11d11bcU, 0x25dc2239U, 0x4ef6e4eeU, 0x6aca5d27U, 0xf09053edU, 0x036c90d3U };
static const uint32_t A4[NL] = { 0xbbd6a29aU, 0xaa17f8ebU, 0x7561e862U, 0xa0f67f7bU, 0x5ab296ceU, 0xfc2414fbU, 0x00db2434U };
static const uint32_t A5[NL] = { 0xd50c7002U, 0xc8d67492U, 0xd4b0dd68U, 0x13a3b83aU, 0x4556eb01U, 0x98d40432U, 0x002bd40aU };
static const uint32_t A6[NL] = { 0xe1655739U, 0x809df6f7U, 0x8ff04c0eU, 0x6efe0ef3U, 0x2d4ee013U, 0xc4235d34U, 0x00074e01U };
static const uint32_t A7[NL] = { 0x217bc226U, 0x6d6733daU, 0x7aea2ff9U, 0xa1b0507fU, 0x2cae78f4U, 0xd2e07acdU, 0x00010b24U };

/* CO[k] = A_k * 2^(XDEN*(7-k)), the coefficients of Horner's rule on V. */
static uint32_t CO[8][NL];

static void init_coeffs (void)
{
  const uint32_t *src[8] = { A0, A1, A2, A3, A4, A5, A6, A7 };
  int k;
  for (k = 0; k < 8; k++)
    {
      big_set (CO[k], src[k]);
      big_shl (CO[k], XDEN * (7 - k));
    }
}

/* V = P(x) * 2^VDEN for x = (Cc + d) / 2^XDEN.  Horner, with a signed d. */
static void poly_eval (int64_t d, uint32_t *V)
{
  uint32_t t[NL];
  uint32_t dlo, dhi;
  int neg = 0;
  int k;

  if (d < 0)
    {
      neg = 1;
      d = -d;
    }
  dlo = (uint32_t) (d & 0xffffffffLL);
  dhi = (uint32_t) (d >> 32);

  big_set (V, CO[7]);
  for (k = 6; k >= 0; k--)
    {
      big_set (t, V);
      big_mul32 (t, dhi);
      big_shl_limb (t);
      big_mul32 (V, dlo);
      big_add (V, t);
      if (neg)
        big_neg (V);
      big_add (V, CO[k]);
    }
}

/* ------------------------------------------------------------- the search */

/* Is x = X / 2^XDEN a hard-to-round case: are the MHRC bits following the
 * round bit of P(x) all equal?  This is htr.c's check(), without MPFR. */
static int is_hard (int64_t X)
{
  uint32_t V[NL];
  uint64_t top;
  poly_eval (X - CCNUM, V);
  top = big_bits64 (V, TOPBIT) & ((((uint64_t) 1) << MHRC) - 1);
  if (top == 0)
    return 1;
  if (top == ((((uint64_t) 1) << MHRC) - 1))
    return big_low_nonzero (V, TOPBIT);
  return 0;
}

unsigned long long candidates = 0, found = 0;

int main (void)
{
  uint32_t V[NL];
  int64_t X = X0NUM;
  uint64_t n = ((uint64_t) 1) << LOG2N;

  init_coeffs ();

  while (X < X1NUM)
    {
      uint64_t A, B, E, twoE, i;

      poly_eval (X - CCNUM, V);
      E = big_bits64 (V, ESHIFT) + (((uint64_t) 1) << (64 - MHRC));
      A = big_bits64 (V, ASHIFT) + E;          /* wraps mod 2^64 */
      B = big_bits64 (V, BSHIFT);
      twoE = 2 * E;

      for (i = 0; i < n; i++)
        {
          if (A < twoE)
            {
              candidates++;
              if (is_hard (X + (int64_t) i))
                {
                  found++;
                  printf ("%lld/2^54\n", (long long) (X + (int64_t) i));
                }
            }
          A = A + B;                           /* wraps mod 2^64 */
        }
      X = X + (int64_t) n;
    }

  printf ("%llu candidates, found %llu hard-to-round\n", candidates, found);
  return 0;
}
