# Triple words on primitive floats

A **triple word** is three binary64 floats `TWFloat x0 x1 x2` standing for the
real number `x0 + x1 + x2`. Three words hold about 48 decimal digits where one
holds 16 and two hold 32.

Rocq already gives primitive floats an interface — the operations and the
theorems that say what they compute. The goal here is an interface of the same
kind for triple words, so that a proof can be carried out over them instead.
`tw_ops.v` is that interface. It is the same exercise as `code/ddouble`, one
word further up.

The algorithms are those of the three-word paper, whose Rocq proofs are kept
in `threewords/`.

## The state of it

**The shape is checked; the arithmetic is not.** `tw_ops.v` builds a module
`TwFloat` and the sealing at the bottom of that file,

```coq
Module TwFloatCheck <: FloatOps := TwFloat.
```

is what says it meets Interval's signature. But every obligation that needs a
fact about the arithmetic is `Admitted`, and they are listed at the top of the
file. Nothing here may be relied on until that list is empty. It is built in
this order so that the whole chain — up to Interval's own tactic over triple
words — can be assembled and measured before it is proved, which is the order
the double-word work went in as well.

## Building

On the `native` switch (Rocq 9.1.1), with `coq-interval` and `coq-flocq`
installed there.

```
make
```

The `Makefile` comes from `_CoqProject` by `coq_makefile`; add any new file to
`_CoqProject`.

## What the arithmetic delivers

Measured on this desktop, by running the files below.

| | value |
|---|---|
| pi by Machin, plain operations (`test_pi.v`) | right to **48.5 digits**, `2^-161` |
| `div_DN`/`div_UP` on 1/3 and 22/7 | `2^-158` apart |
| `sqrt_DN`/`sqrt_UP` on 2 | `2^-158` apart |
| `add_DN`/`add_UP` on 2 pi | `2^-162` apart |
| `fromZ_DN`/`fromZ_UP` on a 50-digit whole number | `2^-166` either side |

The same numbers for two words are `2^-97`.

## Two things the port settled

**Rocq's primitive floats have no fused multiply-add.** So Algorithms 9, 13
and 15 cannot be transcribed as the paper writes them: every step of the form
`RN(a + b * c)` becomes two roundings here, and the error-free product is
Dekker's splitting rather than the one instruction. The paper's *bounds*
survive that change; the paper's *values* do not. Nothing is lost for our
purpose, because what is asked of these operations is only a bound, and the
seed of a division or a root is never trusted at all.

**The two sweeps want their terms in order of decreasing size.** This is not
a tidying matter, and getting it wrong is invisible — the answer is still a
triple word, just fifty bits short.

* What one sweep leaves can have two terms of the same size next to each
  other, so the second sweep is what separates them. Cutting an expansion to
  three words before that second sweep rounds at the size of the *second*
  word and costs the whole of the third. Measured: `2^-105` instead of
  `2^-161`.
* `Merge` puts the sum's six terms in order. The product's thirteen have no
  fixed order — which is largest depends on the two triple words — so they
  are sorted at run time by `sortMag`. Without it the product came out
  `2^-110` instead of `2^-160`.

Both were found by the pi test, not by reading.

## And one trap

`Z.ldexp` is not the scaling it looks like. Interval carries a
`Compat.ldexp f _ := f` for the versions of Rocq whose floats had no scaling,
and a bare `Z.ldexp` picks **that** one up and silently returns its argument.
The real one is `FloatOps.Z.ldexp`, and `ldexp2` in `tw_ops.v` is the name
written out so it cannot happen twice. It cost `fromZ` an entire word before
the test caught it.

## The files

| file | what it holds |
|---|---|
| `twarith.v` | the algorithms: the error-free transforms, the two sweeps, `sortMag`, `Merge`, and the operations rounded to nearest |
| `tw_updn.v` | the directed operations: the widening steps and the up and down forms of each |
| `tw_ops.v` | the interface: `TwFloat`, its obligations, and the sealing |
| `test_pi.v` | a smoke test: pi by Machin, and what the interface's operations bracket |
| `tw_unsafe.v` | `sensible_format := true` with `div2` admitted, so Interval's functors apply |
| `threewords/` | the paper's development, copied untouched. Nothing on the build path depends on it |

## How a bound is got

The same three rules the double-word work settled on, and they carry over
unchanged.

**An overflow travels; do not test for it.** An infinity plus anything is an
infinity, so a chain that ran out of range ends in one and the final `real`
test sees it. `upFp` and `dnFp` leave alone the infinity they would undo, and
after that no operation needs a guard of its own.

**Bound the result for an arbitrary seed, then apply it.** Division and the
root take their `q` from an algorithm nothing is proved about — long division
for the one, two Newton steps for the other. The bound is the residual:
whatever `q` is, the true quotient is within `|x - q*y| / |y|` of it, and the
root within `(x - q*q) / q`. So the seed is free to change, and the
FMA-free transcription of the paper's algorithms costs nothing.

**A test is for what propagation cannot settle.** Division keeps one — the
divisor bounded away from zero. The root keeps two: the same one, and the
sign of what it is given.

## Interval will not take it, and why

The same reason as for two words, and worse. `div2_correct` asks that halving
be exact above `1/256`, and that is a statement about the sum of the words:
it bounds the leading word away from zero and says nothing about the last one.
`sensible_format` is therefore `false`, and Interval's three functors all
require it `true`. `tw_unsafe.v` sets it `true` and admits `div2_correct`,
which is **false**, so that the arithmetic can be measured through Interval
before the format is narrowed. A number computed through that module is a real
number; a theorem obtained through it is worth nothing.

The way through, when someone takes it, is to narrow the format: a triple stops
counting as a triple word when its last word is subnormal.

## What is next

1. **The bench.** Interval's own goals sit at `i_prec 60`–`90`, all of which a
   double word already covers, so they say nothing about three words. New
   goals are needed, in three bands:

   | band | what to compare |
   |---|---|
   | small | primitive floats, bignums, double words |
   | higher | bignums, double words |
   | higher still | bignums, triple words |

   Warm-up bites: never report the first heavy call in a file.

2. **The obligations.** The list at the top of `tw_ops.v`, one at a time.
