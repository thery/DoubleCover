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
Dekker's splitting rather than the one instruction. So the paper's *constants*
do not carry over as they stand, and the number of units in the last place
that the bound shifts by is measured here rather than taken from the paper —
`probek.py` does that, on forty thousand random triple words.

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

**Bound by shifting, not by computing.** An algorithm known to be within k
units in the last place needs no residual: the enclosure is the answer shifted
k up and k down, which is one exponent change. That is what Interval's own
primitive-float module does — `next_up (x + y)` — and it works there because
the hardware is correctly rounded, so one unit suffices. A triple word is not
correctly rounded, so it is the same with k = 8.

This is a trade, and it went the other way at first. The residual —
`|x - q*y| / |y|` for the quotient, `(x - q*q) / q` for the root — asks
*nothing* of the algorithm that produced `q`, so it needed no theorem at all.
It also cost two triple-word products and two subtractions on every call:
measured, five times the quotient itself and eight times the root. The shift
needs a theorem in exchange, and it is a theorem this file does not yet have.

**The shift holds in the normal range only**, because the paper's bounds are
proved in the format with no smallest exponent. Below that a fixed step is
used, which needs no error analysis: down there every number is a whole
multiple of the smallest float, so an operation can only be out by one of
them. `code/ddouble` is not in that position — its own proofs are in the
bounded format, subnormals included, so its shift needs no range test.

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

## The bench

Three files, none on the build path. Build `code/ddouble` first, then

```
coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith bench_ops.v
coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith bench_bands.v
coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith bench_lift.v
```

`bench_ops.v` times the arithmetic with no tactic above it; `bench_bands.v`
times Interval's tactic over each arithmetic; `bench_lift.v` is the one goal
in Interval's own sources that asks for more than a double word.

Interval's tactic decides which arithmetic runs by whether `i_prec` is given
at all (`src/Tactic.v:80`): **without** it the tactic uses primitive floats at
53 bits, hardwired, whatever module it was built on; **with** it, that module.
For the two word modules the number asked for changes nothing about the
arithmetic — `PtoP` throws it away — but it does tell the transcendental code
how many bits to aim for.

### One operation at a time

`bench_ops.v`, ten thousand operations each (a thousand for the root), this
desktop, seconds. Bignums are asked for the precision each word module
actually holds, so this is a comparison at equal precision.

| op | bignum 107 | bignum 159 | double words | triple words |
|---|---|---|---|---|
| add | 0.053 | 0.088 | **0.008** | 0.036 |
| mul | 0.091 | 0.169 | **0.013** | 0.104 |
| div | 0.247 | 0.924 | **0.016** | 0.133 |
| sqrt | 0.025 | 0.046 | **0.002** | 0.018 |

Against bignums at the same precision, and both win on all four:

| | add | mul | div | sqrt |
|---|---|---|---|---|
| double words | 6.6x faster | 7.0x faster | 15.4x faster | 12.5x faster |
| triple words | 2.4x faster | 1.6x faster | 6.9x faster | 2.6x faster |

**AN EXPONENT SHIFT IS NOT ONE INSTRUCTION HERE.** The step was first written
as `FloatOps.Z.ldexp`, which is one instruction on the machine and exact. In
Rocq's evaluator it is nothing of the kind: it goes through `Z.max`, `Z.min`
and a conversion of a whole number to a machine integer on every call.
Measured, **4.8 µs against 0.2 µs** for a float multiplication that gives the
identical answer — and the constant is a power of two, so the multiplication
is exact as well. That one line was hiding almost the whole gain: the
double-word division read 0.071 with it and 0.016 without.

Two changes got the quotient and the root there. The bound is a shift of eight
units in the last place instead of a computed residual, and the algorithms are
the paper's (`twpaper.v`) instead of mine. Timed on their own, the paper's
root is 16.5 µs against 43.5 for Newton's method, and its quotient 10.5 µs
against 19 for long division — so the paper's are 2.6 and 1.8 times quicker as
well as tighter.

**THE RESULT: a double word is quicker than bignums at every operation. A
triple word is quicker at the two that matter most and slower at the other
two.** The sum and the product are where three words pay: both are one sweep
over an expansion and nothing else. The quotient and the root are where the
implementation is extravagant rather than the idea wrong — `divTwTw` is three
rounds of long division, each doing a *full* triple-word multiplication, and
`sqrtTw` is two Newton steps each containing one of those divisions. The
paper's Algorithms 13 and 15 do the same work in a fraction of that, and
nothing about the bounds would change if they were used: division and the root
are bounded by their residual, so the seed is free to be anything.

Beside a double word, a triple word costs 4.4x on the sum, 9.5x on the
product, 12.7x on the quotient and 24x on the root.

**This table was wrong twice before it was right.** The first version had the
multiplier written as a call, `mult p`, inside each loop body, so every
iteration recomputed a division and two conversions — and the *addition* row
then read tenfold against the double word, which is what made thery say it
was counter-intuitive. It was. A loop that times an operation must hold every
other value it touches constant, and 2000 iterations was too few to read
anyway.

### Through the tactic

`bench_bands.v`, seconds, and `refused` is Interval reporting *"Numerical
evaluation failed to conclude"* — a bound too wide for the goal, never a wrong
answer.

| goal | bits asked | floats | bignums | double words | triple words |
|---|---|---|---|---|---|
| pi to 14 digits | 47 | 0.054 | 0.064 | **0.014** | 0.018 |
| pi to 24 digits | 82 | refused | 0.068 | **0.019** | 0.023 |
| pi to 34 digits | 105 | refused | 0.034 | refused | **0.026** |
| pi to 45 digits | 150 | refused | 0.039 | refused | **0.037** |
| Interval's own 120-bit goal | 120 | — | **0.169** | refused | refused |
| `method_error` | 80 | — | 5.824 | **1.575** | refused |
| `poly_error` | 90 | — | 0.122 | **0.108** | 0.135 |
| `cancellation`, depth 20 | 60 | — | 76.6 | **38.7** | 207.0 |

Three things to read off it. **Triple words are the only arithmetic that takes
the 105- and 150-bit brackets at all**, and since the shift replaced the
residual they take them quicker than bignums take the ones bignums can do.
**`cancellation` is where the per-operation table shows through**: its cost is
the splitting, so precision buys nothing, and the sum and the product — which
the shift did not touch — are paid in full. And **a double word is quickest
wherever it reaches at all**, which is up to about a hundred bits.

### What each arithmetic really delivers

Relative width of the enclosure, `interval_intro ... with (i_prec 107)`:

| quantity | bignums | double words | triple words |
|---|---|---|---|
| `PI` | 2^-106.6 | 2^-100.5 | 2^-155.5 |
| `1/3` | 2^-106.6 | 2^-101.6 | 2^-157.8 |
| `sqrt 2` | — | 2^-101.6 | 2^-157.5 |
| `exp 1` | — | 2^-95.7 | 2^-150.2 |
| a 25-digit rational | 2^-106.6 | 2^-101.1 | 2^-158.7 |

Nominal precision is 107 and 159; both modules lose five to nine bits across a
whole evaluation, which is what their error bounds allow. This table is how
the `fromZ` fault in `code/ddouble` was found — its 25-digit row read
`2^-78.3`, twenty-three bits out of line with every other row in its own
column, and that is now fixed (`fromZ` used to widen by an integer `1`, which
is an absolute step and so `1/n` in relative terms).

## Open

1. **`method_error` and Interval's 120-bit goal are refused, and it is not
   understood.** What has been ruled out, each by measurement:
   * *Not precision.* At a point this module encloses `f t - exp t` to
     `6.4e-47` where a double word gives `4.1e-30` and bignums `1.3e-31`.
   * *Not the Taylor model of a quotient*, the only thing `method_error` has
     that `poly_error` has not: both modules prove
     `Rabs (x/(1+x) - x*(1-x)) <= 3/10` under `i_bisect`/`i_taylor` in 70 ms.
   * *Not a margin.* The same goal is refused with the bound loosened twenty
     times over, to `1e-16`, while a bound of `1` is proved.
   * *Not `mag`.* It is one bit wider than the double-word one (`-97` against
     `-98` on `1e-30`), and `PrimitiveFloat.mag 0` is `-2101`, so the `Z.max`
     is safe.
   * *Not `midpoint` or `wellFormed`.* Both are `real` on the values tried.
2. **Speed, and it is the BOUND that costs, not the algorithm.** Timed on
   their own, microseconds a call:

   | | µs |
   |---|---|
   | `plusTwTw` | 3 |
   | `timesTwTw` | 9 |
   | `divTwTw`, three rounds of long division | 21 |
   | `sqrtTw`, two Newton steps, rounded to nearest | 52 |
   | `mulTwUp` | 10 |
   | `divTwUp` | **101** |
   | `sqrtTwUp` | **436** |

   The seed is cheap. The residual bound costs five times the seed for the
   quotient and eight times for the root — and the four operations it performs
   (`mulTwDn q q`, `mulTwUp q q` and two subtractions) come to about 26 µs by
   the rows above, so roughly 350 µs of the root's 436 is unaccounted for.
   The likely cause is that `q` is recomputed rather than shared across its
   three uses in the `let:` chain of `sqrtTwErr`. That is the first thing to
   measure, and it is worth more than anything in the algorithms.

   **Where the sum's time goes**, µs a call, each pass timed on top of the one
   before:

   | | cumulative | this pass |
   |---|---|---|
   | one `twoSum`, the unit of cost | 0.2 | |
   | `Merge`, and building the two three-lists | 0.7 | 0.7 |
   | and `vecSum` | 1.4 | 0.7 |
   | and `vseb` | 2.1 | 0.7 |
   | and `expUp`'s cut and separation | 2.7 | 0.6 |

   A double word's sum is 0.8 µs and does **three** two-sums. This does
   **eleven**, and spends a quarter of its time building lists before any
   arithmetic happens: eleven times 0.2 plus 0.7 is 2.9 against 2.7 measured,
   so nothing is unexplained. Two savings, neither of which touches a bound:
   `expUp` separates a second time after cutting, which is 22 per cent and
   goes away if the tail is folded in *before* the single separation; and the
   `seq` representation is another 26 per cent. That would be about 1.4 µs,
   within 1.8 times a double word, which is what one more word should cost.
3. **The obligations.** The list at the top of `tw_ops.v`, one at a time.
