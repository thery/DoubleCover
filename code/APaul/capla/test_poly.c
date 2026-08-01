/* test_poly.c -- driver for poly.b.
 *
 * The reference is htr_plain.c's own big_* layer and poly_eval, copied
 * here verbatim; the Capla side is compared against it limb by limb, at
 * points spread over the whole search interval.
 */

#include <stdint.h>
#include <stdio.h>

#define NL      21            /* limbs of 32 bits                          */
#define XDEN    54            /* grid scale: x = X / 2^XDEN                 */
#define MHRC    35            /* identical bits required after the round bit */
#define VDEN    (220 + 7 * XDEN)           /* = 598, scale of V             */
#define PBITS   (VDEN - 53)                /* = 545, the round-bit position */
#define LOG2N   20                         /* chunk size n = 2^LOG2N        */
#define DDEXP   (2 * (-1 - 53) + (54 - 1) - 1 + 2 * LOG2N)      /* = -16    */
#define ESHIFT  (VDEN - DDEXP - 64)        /* = 550                         */
#define ASHIFT  (PBITS - 64)               /* = 481                         */
#define BSHIFT  (VDEN + 1 - 64)            /* = 535                         */
#define TOPBIT  (PBITS - MHRC)             /* = 510                         */

#define X0NUM  4503599627370496LL          /* 0.25                          */
#define X1NUM  4503779771355591LL          /* 0.25001, as a double          */
#define CCNUM  4503689699363044LL          /* expansion centre c * 2^XDEN   */

/* Capla's [[u32; n]; 8] is an array of row pointers, uint32_t**, not a
 * flat block; only the multi-dimensional [u32; 8, n] would be flat.  So
 * the table is passed as 8 pointers into the rows. */
extern void init_coeffs (uint32_t **CO, uint64_t n);
extern void poly_eval (int64_t d, uint32_t *V, const uint32_t **CO,
                       uint32_t *t, uint64_t n);
extern uint64_t big_bits64 (const uint32_t *a, uint64_t p, uint64_t n);
extern uint8_t big_low_nonzero (const uint32_t *a, uint64_t p, uint64_t n);

/* ------------------------------------- the reference, from htr_plain.c */

static void ref_set (uint32_t *r, const uint32_t *a)
{
  int i;
  for (i = 0; i < NL; i++)
    r[i] = a[i];
}

static void ref_add (uint32_t *r, const uint32_t *a)
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

static void ref_mul32 (uint32_t *r, uint32_t m)
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

static void ref_shl_limb (uint32_t *r)
{
  int i;
  for (i = NL - 1; i > 0; i--)
    r[i] = r[i - 1];
  r[0] = 0;
}

static void ref_shl (uint32_t *r, int n)
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

static void ref_neg (uint32_t *r)
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

static uint64_t ref_bits64 (const uint32_t *a, int p)
{
  int limb = p / 32;
  int bits = p % 32;
  uint64_t lo = (uint64_t) a[limb] | ((uint64_t) a[limb + 1] << 32);
  if (bits == 0)
    return lo;
  return (lo >> bits) | ((uint64_t) a[limb + 2] << (64 - bits));
}

static int ref_low_nonzero (const uint32_t *a, int p)
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

static const uint32_t A0[NL] = { 0xbfcd8b33U, 0xa2766a2aU, 0x1fa1f522U, 0xd9c95d93U, 0x80be2eebU, 0xa361f790U, 0x148b64f7U };
static const uint32_t A1[NL] = { 0xceaedbbcU, 0xa47b8f34U, 0x1fa1f522U, 0xd9c95d93U, 0x80be2eebU, 0xa361f790U, 0x148b64f7U };
static const uint32_t A2[NL] = { 0x15ac5fd8U, 0x4593777aU, 0x351b3ee6U, 0xece4aeccU, 0x405f1775U, 0xd1b0fbc8U, 0x0a45b27bU };
static const uint32_t A3[NL] = { 0x02965a86U, 0xe11d11bcU, 0x25dc2239U, 0x4ef6e4eeU, 0x6aca5d27U, 0xf09053edU, 0x036c90d3U };
static const uint32_t A4[NL] = { 0xbbd6a29aU, 0xaa17f8ebU, 0x7561e862U, 0xa0f67f7bU, 0x5ab296ceU, 0xfc2414fbU, 0x00db2434U };
static const uint32_t A5[NL] = { 0xd50c7002U, 0xc8d67492U, 0xd4b0dd68U, 0x13a3b83aU, 0x4556eb01U, 0x98d40432U, 0x002bd40aU };
static const uint32_t A6[NL] = { 0xe1655739U, 0x809df6f7U, 0x8ff04c0eU, 0x6efe0ef3U, 0x2d4ee013U, 0xc4235d34U, 0x00074e01U };
static const uint32_t A7[NL] = { 0x217bc226U, 0x6d6733daU, 0x7aea2ff9U, 0xa1b0507fU, 0x2cae78f4U, 0xd2e07acdU, 0x00010b24U };

static uint32_t refCO[8][NL];

static void ref_init_coeffs (void)
{
  const uint32_t *src[8] = { A0, A1, A2, A3, A4, A5, A6, A7 };
  int k;
  for (k = 0; k < 8; k++)
    {
      ref_set (refCO[k], src[k]);
      ref_shl (refCO[k], XDEN * (7 - k));
    }
}

static void ref_poly_eval (int64_t d, uint32_t *V)
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

  ref_set (V, refCO[7]);
  for (k = 6; k >= 0; k--)
    {
      ref_set (t, V);
      ref_mul32 (t, dhi);
      ref_shl_limb (t);
      ref_mul32 (V, dlo);
      ref_add (V, t);
      if (neg)
        ref_neg (V);
      ref_add (V, refCO[k]);
    }
}

/* --------------------------------------------------------------- checks */

static void show (const char *what, const uint32_t *a, const uint32_t *b)
{
  int i;
  printf ("  %s differ:\n    C     ", what);
  for (i = NL - 1; i >= 0; i--)
    printf ("%08x", a[i]);
  printf ("\n    Capla ");
  for (i = NL - 1; i >= 0; i--)
    printf ("%08x", b[i]);
  printf ("\n");
}

#define NPT 9                          /* points tested across the interval */

int main (void)
{
  uint32_t CO[8][NL], V[NL], t[NL], refV[NL];
  uint32_t *COp[8];
  int64_t pts[NPT];
  int i, k, bad = 0;

  for (k = 0; k < 8; k++)
    COp[k] = CO[k];

  ref_init_coeffs ();
  init_coeffs (COp, NL);

  /* the coefficient tables must agree, table entry by table entry */
  for (k = 0; k < 8; k++)
    for (i = 0; i < NL; i++)
      if (refCO[k][i] != CO[k][i])
        {
          printf ("CO[%d] mismatch\n", k);
          show ("CO", refCO[k], CO[k]);
          bad = 1;
          break;
        }
  if (!bad)
    printf ("init_coeffs: 8 coefficients agree\n");

  /* the two ends of the interval, the centre, and points in between */
  pts[0] = X0NUM;
  pts[1] = X1NUM - 1;
  pts[2] = CCNUM;
  pts[3] = CCNUM - 1;
  pts[4] = CCNUM + 1;
  for (i = 5; i < NPT; i++)
    pts[i] = X0NUM + (X1NUM - X0NUM) * (i - 4) / (NPT - 3);

  for (i = 0; i < NPT; i++)
    {
      int64_t d = pts[i] - CCNUM;
      int j, same = 1;

      ref_poly_eval (d, refV);
      poly_eval (d, V, (const uint32_t **) COp, t, NL);
      for (j = 0; j < NL; j++)
        if (refV[j] != V[j])
          same = 0;
      if (!same)
        {
          printf ("poly_eval at d = %lld:\n", (long long) d);
          show ("V", refV, V);
          bad = 1;
          continue;
        }

      /* the four windows the search reads out of V, and the low test */
      {
        int shifts[4] = { TOPBIT, ASHIFT, BSHIFT, ESHIFT };
        for (j = 0; j < 4; j++)
          {
            uint64_t w = ref_bits64 (refV, shifts[j]);
            uint64_t g = big_bits64 (V, (uint64_t) shifts[j], NL);
            if (w != g)
              {
                printf ("big_bits64 at %d, d = %lld: C %llu, Capla %llu\n",
                        shifts[j], (long long) d,
                        (unsigned long long) w, (unsigned long long) g);
                bad = 1;
              }
          }
        if (ref_low_nonzero (refV, TOPBIT) != big_low_nonzero (V, TOPBIT, NL))
          {
            printf ("big_low_nonzero at d = %lld differ\n", (long long) d);
            bad = 1;
          }
      }
    }

  if (!bad)
    printf ("poly_eval: %d points agree, with their four windows\n", NPT);
  printf (bad ? "FAILED\n" : "all agree\n");
  return bad;
}
