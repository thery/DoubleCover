// The parameters of eval_fix.c.

#include <stdint.h>

#define FIX_P 200    // bits after the point of every fixed-point number
#define FIX_TAB 256  // table size: x = (256 k + j) ln2/256 + r
#define FIX_LG 32    // extra bits of ln2/256, so that N * ln2/256 is exact
                     // to 2^-FIX_P for |N| < 2^32
#define FIX_DEG 13   // degree of the Taylor polynomial of exp(r)
#define FIX_NL 8     // a number is FIX_NL limbs of 32 bits, lowest first:
                     // 256 bits, in two's complement when it has a sign
