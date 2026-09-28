// The parameters of the Tang evaluator of htr2_fix.c.

#include <stdint.h>

#define TG_P 448     // bits after the point of every fixed-point number
#define TG_TAB 256   // table size: x = (256 k + j) ln2/256 + r
#define TG_LG 32     // extra bits of ln2/256, so that N * ln2/256 is exact
                     // to 2^-TG_P for |N| < 2^32
#define TG_DEG 30    // degree of the Taylor polynomial of exp(r):
                     // |r|^31 / 31! < 2^-407 for |r| <= 2^-9.5
#define TG_ERR 399   // designed error of y: 2^-399, relative
#define TG_NL 16     // a number is TG_NL limbs of 32 bits, lowest first:
                     // 512 bits, in two's complement when it has a sign
