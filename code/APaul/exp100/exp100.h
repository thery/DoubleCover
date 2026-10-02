// exp100: an enclosure of exp(x) to about 156 bits, and the filter
// maybe_hard, in plain C on uint64_t words, written to be proved with VST.
//
// A number is NL limbs of 32 bits, least significant first, each limb held
// in a uint64_t word (so that a 32 x 32-bit product plus two limbs never
// overflows a word: no 128-bit type, which CompCert does not have).  A
// fixed-point number a stands for a 2^-P.

#ifndef EXP100_H
#define EXP100_H

#include <stdint.h>

#define NL 6          // limbs of a number: 192 bits
#define P 160         // bits after the point; 32 bits before it
#define LIMB 32       // bits of a limb
#define MASK 0xffffffffUL
#define K 6           // table of 2^(j/64): x = (64 h + j) ln2/64 + r
#define TAB 64        // 2^K
#define DEG 16        // degree of the Taylor polynomial of exp(r)
#define EXP100_D 16   // error bound of the enclosure, in units of 2^s
#define M_HARD 43     // hard: exp(x)/v within 2^-M_HARD of an integer
#define EMIN (-1022)  // smallest normal exponent of a double
#define PREC 53       // bits of a double

// Enclosure of exp(x), x given by its 64 bits xb (a double in binary64),
// with |x| < 1024 (finite; zero and subnormal x are accepted).
// On success, returns 0 and writes M (3 words of 64 bits, least
// significant first, 2^160 <= M < 2^162) and s such that
//   | exp(x) - M 2^s | <= EXP100_D 2^s,
// a relative error below 2^-156.  Returns a nonzero code when |x| >= 1024,
// x is not finite, or a run-time check of the reduction fails (never seen
// in the tests).
int exp_encl_bits(uint64_t xb, uint64_t *M, int64_t *s);

// The same on a double: reads its bits (not part of the verified code).
int exp_encl(double x, uint64_t *M, int64_t *s);

// The filter: returns 0 only if exp(x)/v is at distance more than 2^-43
// from every integer, for every value of the enclosure (so x is not hard
// in the sense of code/exptablekl/ExpHard.v); returns 1 otherwise
// ("maybe hard"), and also whenever the enclosure fails or the binade of
// exp(x) is not fixed by the enclosure.  Meaningful on the range of the
// tables, -745.14 < x < 709.79; outside it, 1 may be returned for every x.
int maybe_hard_bits(uint64_t xb);
int maybe_hard(double x);

#endif
