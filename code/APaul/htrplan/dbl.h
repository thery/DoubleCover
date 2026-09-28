// Doubles (binary64), read and built from their 64 bits, with no library:
// what Programs 2 and 3 use instead of libm's frexp, ldexp and nextafter.
// A failed check stops the program with the compiler's trap.

#include <stdint.h>

#define assert(c) do { if (!(c)) __builtin_trap (); } while (0)

union dbits { double d; uint64_t u; };

// 2^E, for -1022 <= E <= 1023
static inline double
pow2 (int E)
{
  union dbits b;
  b.u = (uint64_t) (E + 1023) << 52;
  return b.d;
}

// v 2^E, as ldexp: exact while v 2^E is normal, rounded once otherwise
static inline double
dscale (double v, int E)
{
  if (E > 1023) { v *= pow2 (1023); E -= 1023; }
  if (E < -1022) { v *= pow2 (-1022); E += 1022; }
  return v * pow2 (E);
}

// the exponent e of v, 2^(e-1) <= |v| < 2^e, as frexp; v normal
static inline int
dexpo (double v)
{
  union dbits b;
  b.d = v;
  int be = (b.u >> 52) & 0x7ff;
  assert (be != 0 && be != 0x7ff);
  return be - 1022;
}

// the double just below v, as nextafter (v, -infinity); v finite
static inline double
dpred (double v)
{
  union dbits b;
  b.d = v;
  if (v > 0) b.u --;
  else if (v < 0) b.u ++;
  else b.u = 0x8000000000000001ul;             // -0 and +0: -2^-1074
  return b.d;
}
