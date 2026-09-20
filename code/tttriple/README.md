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

**The shape is checked and so is the arithmetic.** `tw_ops.v` builds a
module `TwFloat` and the sealing at the bottom of that file,

```coq
Module TwFloatCheck <: FloatOps := TwFloat.
```

is what says it meets Interval's signature. **Every one of its obligations is
proved**; nothing in it is `Admitted`. Four of them — the quotient and the
root, each way — lean on one named assumption each, and those two are the only
things assumed anywhere. The list is at the top of the file. **What the root's
assumption asks for is now proved** (`threeSqRt_error` in `twflx.v`), bar the
range guard that the scaling would discharge; see *The root, without a fused
multiply-add* below. The quotient's is still measured only.

**The sum, the difference and the product are proved** — `add_UP_correct`,
`add_DN_correct`, `sub_UP_correct`, `sub_DN_correct`, `mul_UP_correct`,
`mul_DN_correct`, from `twbound.v`, admit-free. **They take nothing from the
paper**, and they could not: the paper is proved for round to nearest
throughout and these round in a direction. They do not have to. `Merge` and
`sortMag` move the terms about, `vecSum` and `vseb` are sweeps of `twoSum`
which is exact, so the only step that loses anything is the cut down to three
words, and the cut is made in the direction wanted. The product adds one thing:
what its four two-products can miss, which `twoProd_err` bounds by three and a
half of the smallest number there is apiece — fourteen against the sixteen of
`teps`.

**Both are uniform and neither has a guard.** No range condition enters, so
none is tested: `twoSum` is exact in the bounded format, subnormals included,
and a two-product's miss is bounded absolutely rather than relatively. That is
what separates these six from the quotient and the root, which lean on the
paper's FLX analysis and so keep one. It is built
in this order so that the whole chain — up to Interval's own tactic over triple
words — can be assembled and measured before it is proved, which is the order
the double-word work went in as well.

**The reading is proved.** `realE`, `real_fin` and `toX_real` say when a triple
denotes a real number and which one — all three of its words are numbers and
the triple is one, and then it denotes their sum. Every bound on the
arithmetic will be read into the signature's shape through those, so they come
first. With them, `zero_correct`, `real_correct` and `fromZ_correct` are
proved.

**A whole number enters exactly, or all but the last float.** `fromZ_UP_correct`
and `fromZ_DN_correct` are proved. A whole number is peeled twice: the top
fifty-three bits, the next fifty-three, and what is left. Each peeling is done
on the whole number and not on a float — what comes off is an integer below
two to the fifty-third, which one float holds, times a power of two, and
`ldexp2_exact` says that scaling a float by a power of two is either exact or
an infinity. So neither peeling estimates anything, and the only bound in the
answer is the one the primitive float's own `fromZ_UP` gives on what is left
over. That is where the three words in the table below come from; putting the
number in the leading word alone would keep fifty-three bits of it and drop
the rest.

The double-word version peels once and with a two-product, so it pays a step
of `deps` for what the product can miss. Nothing of that kind is needed here.

**The quotient and the root are proved from one named assumption each.**
`div_UP_correct`, `div_DN_correct`, `sqrt_UP_correct` and `sqrt_DN_correct` are
no longer admitted. What they lean on is `kstep_div` and `kstep_sqrt` in
`twpaper.v`, and those two say only this: the step the answer is widened by
covers what the algorithm is out by. **The root's half is now proved** — see
below — **and the quotient's is still measured**: `probek.py` runs the two
algorithms on forty thousand random triple words and reports 2.3 units in the
last place for the quotient. Both are stated as assumptions in their own
right, so
`Print Assumptions` on anything reached through the quotient or the root says
`twpaper.kstep_div` in as many words. Before, the same gap was four `Admitted`
obligations, which said nothing about where it lay.

Everything between the assumption and the obligation is proved: the guards
(`divGuard_nz`, `sqrtGuard_pos`), the widening (`widenUp_ge`, `widenDn_le`),
and the reading into Interval's shape. The root's guard is the one that takes
an argument: what it tests is the three words added, and being a triple word
the first addition drops the second word, so the test is on the first and the
third — and the third is at most a quarter of the first, so the leading word
is above nought and with it the value.

**Comparing on the words is wrong, and `tw_cmpbad.v` shows it.** The obvious
rule is the one two words use: take the leading word, and the next when the
ones before agree. For two words that is sound — a double word rounds to its
own leading word, rounding is monotone, so the leading words are in the order
the values are. **A triple word does not round to its leading word.** Being one
is two tests, each on a pair — the second word within half a step of the first,
the third within half a step of the second — and together they do not say that
the first plus the other two rounds back to the first. The smallest case is
one, plus half a step of one, plus half a step of that: the first two are a tie
and round down because one has an even last bit, and the third pushes the sum
past the halfway point.

`tw_cmpbad.v` gives two triple words whose leading words are in one order and
whose values are in the other, and proves it — the two readings are computed
exactly and compared as whole numbers. It is on the build path so the rule
cannot come back.

**So `cmp` reads the value, and it reads it in two goes.** The value is read
exactly and as a whole number: every binary64 number is a whole number times a
power of two, Interval's own `toF` hands over both halves, three of them
brought to a common power add as whole numbers, and two such compare as whole
numbers. Nothing is rounded, so there is no error term and no range condition.

**But reading the value is dear, so it is not done unless it has to be.**
`Prim2SF` gets the mantissa out through `Uint63.to_Z`, which walks sixty-three
bits one at a time — measured, **29 µs a float**, and a comparison reads six of
them. Put in front of Interval's tactic that is not a slowdown but a stop. So
the words are asked first, and they are allowed to answer only when they can
prove it: are the three words the same, and do the leading words differ by more
than the two tails can be worth? The second amount is not guessed, it is added
up — the last two words of each, in absolute value, rounded up. When the gap
clears it the order is settled whatever the tails are.

Measured, per call:

| | µs |
|---|---|
| double-word `cmp` | 0.36 |
| triple-word, the words-only rule (wrong) | 0.66 |
| triple-word, the cheap test — what nearly always fires | 1.50 |
| triple-word, reading the value | 234 |

**And the dear path is rare.** On forty thousand comparisons along a chain of
computed values it never fired once. In `cancellation` — the most
comparison-heavy goal in `bench_bands.v`, a deliberate `exp x - exp x` at
bisection depth twenty — it fired about thirty thousand times out of some
twenty-three million, **0.13%**, so the average is **1.80 µs**. What the whole
goal costs, same machine, same session:

| `cmp` | seconds |
|---|---|
| the words-only rule (wrong) | 191.7 |
| cheap test, cheap fallback | 211.2 |
| cheap test, exact fallback — what is in | **218.1** |

So correctness costs **14% on the worst goal in the suite and nothing on any
other** — the pi brackets are unchanged. Three quarters of that 14% is the
cheap test itself, which fires on every call; only a quarter is the rare exact
path. Against bignums, which is the comparison the tables here make, a
triple-word `cmp` is **2.7x quicker at 107 bits**.

The exact path could be made cheap rather than rare. `threewords/Nonoverlap.v`
proves that for a P-nonoverlapping list the tail after the first term is at
most `2u` of that term's `ufp` — so the sign of the sum is the sign of what
leads it, and sweeping the six words of the difference would settle the order
for about what an addition costs. What is missing is the bridge: that file is
about Flocq reals, `twarith.v`'s `vseb` is about primitive floats, and the
theorem that the sweep produces a non-overlapping list lives on the Flocq side
too. It would remove the worst case; it would not help the average, which the
cheap test already carries.

**The bridge is `code/ddouble`'s, not a copy.** `dwbridge.v` says what one
primitive float is as a real number and what one operation on it does, and
nothing about pairs, so it serves three words as well as two. `tw_ops.v` now
imports it, which means **`code/ddouble` must be built first** — `_CoqProject`
already points at it.

**And so are the pair, the error-free transforms and the widening steps.**
`twoSum`, `fastTwoSum`, `c_const`, `splitC`, `dekker` and `twoProd` were
written out here a second time, and with them a second `dwfloat`. They are the
same lines either way and they say nothing about pairs beyond returning one, so
`twarith.v` now takes all seven from `dwarith.v`, and `tw_updn.v` takes `upFp`,
`dnFp`, `addUpFp`, `addDnFp`, `mulUpFp`, `mulDnFp`, `divUpFp`, `divDnFp` and
`posFp` from `dw_updn.v`; only the two on a difference are new here.

That is not tidying. While the type was declared twice, nothing proved of the
first applied to the second — and what is proved of the first is most of what
the sweeps need: `twoSum` is exact in the bounded format (`dwtwosum.v`), the
two-product misses by at most three and a half of the smallest number there is
(`dwprod.v`), and each widening step is on the right side of what it stands for
(`dwbound.v`). All three now apply here as they stand.

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
| `twpaper.v` | the paper's algorithms on primitive floats: Algorithms 9, 11, 14, 15, 18, 20, and the step |
| `twprodg.v` | Section 6.2 of the paper, made generic in `c` and `z3`, and Algorithm 9 without the fused multiply-add |
| `twseed.v` | the seed, the two products and the root, all with nothing fused: `ThreeSqRtNn_error` |
| `twflx.v` | the bridge, primitive floats to the paper's reals, ending in `threeSqRt_error` |
| `tw_cmpbad.v` | the pair that shows comparing on the words is wrong, and that `cmp` gets it right |
| `test_pi.v` | a smoke test: pi by Machin, and what the interface's operations bracket |
| `tw_unsafe.v` | `sensible_format := true` with `div2` admitted, so Interval's functors apply |
| `threewords/` | the paper's development, copied untouched. Builds on its own (`cd threewords && make`); nothing else on the build path depends on it yet |

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
| add | 0.052 | 0.089 | **0.009** | 0.042 |
| mul | 0.092 | 0.155 | **0.012** | 0.115 |
| div | 0.256 | 0.871 | **0.017** | 0.136 |
| sqrt | 0.025 | 0.047 | **0.003** | 0.014 |
| cmp | 0.448 | 0.318 | **0.055** | 0.162 |

Medians of three runs. The `cmp` row is a hundred thousand comparisons, not ten
thousand: a comparison is far cheaper than an operation. It is the one row
where the three-word column is not the slowest — against bignums at its own
precision a triple-word comparison is 1.8x quicker, and 2.7x quicker than
bignums at 107.

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
| pi to 14 digits | 47 | **0.012** | 0.021 | **0.012** | 0.018 |
| pi to 24 digits | 82 | refused | 0.335 | **0.014** | 0.016 |
| pi to 34 digits | 105 | refused | 0.023 | refused | **0.020** |
| pi to 45 digits | 150 | refused | **0.027** | refused | 0.031 |
| `method_error` | 80 | — | 5.047 | **1.239** | refused |
| `poly_error` | 90 | — | 0.057 | **0.047** | 0.095 |
| `cancellation`, depth 20 | 60 | — | 74.8 | **23.5** | 213.8 |

One run, after the comparison was fixed. Interval's own 120-bit goal is not in
`bench_bands.v` and is not in this table any more; it was 0.169 for bignums
against 0.174 for triple words when it was measured by hand.

Three things to read off it. **Double words and floats do not reach the 105-
and 150-bit brackets at all**, and triple words do, at a cost that is within a
few per cent of what bignums pay for the same brackets — bignums take the
150-bit one slightly quicker, 0.027 against 0.031, and triple words take the
105-bit one slightly quicker the other way. **`cancellation` is where the
per-operation table shows through**: its cost is the splitting, so precision
buys nothing, and the sum and the product — which the shift did not touch — are
paid in full. And **a double word is quickest wherever it reaches at all**,
which is up to about a hundred bits.

`cancellation` is also the one goal the comparison being fixed cost anything:
the old words-only rule takes 191.7 on this machine, the correct one 213.8.
Every other row is unchanged — see the comparison section above.

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

## The root, without a fused multiply-add

`kstep_div` and `kstep_sqrt` are the only assumptions in the development.
The root is the better of the two to attack, because its range half is a
known manoeuvre: scaling by an **even** power of two is exact on every word,
lands the argument in a fixed binade and brings the answer back by half the
exponent, so every intermediate is normal and the paper's FLX bounds apply
unchanged. `code/ddouble`'s `dwsqrt.v` already does exactly this
(`dsqscale = 2^537`). Division has no such single trick — its quotient's
exponent is unconstrained — and `dwdivflx.v` uses a guard instead.

**Rocq's primitive floats have no fused multiply-add.** Every `RN(v + a w)`
in the paper is two roundings here, `RN(v + RN(a w))`, and there are seven of
them in Algorithm 15: three in the seed, two in Algorithm 11 (`c` and `z31`)
and two in Algorithm 20 (`z31` and `z3`). So the paper's `ThreeSqRt_error` is
about a different program from the one that runs, and the whole chain had to
be re-derived.

**The move that made it tractable.** Section 6.2 — the part that proves the
inner `VecSum` F-nonoverlapping and `VSEB`'s star identity for it — never asks
what `c` and `z3` *are*. It asks four things: that both are in the format,
that `|c| <= 8u^2` and `|z3| <= 12u^2`, and that `|RN(c + z3)|` is within
fifteen `ulp` of the larger of the two middle words. `twprodg.v` is the
paper's own proof text with those two made variables and those four made
hypotheses — nine lemmas, from `s3_le_16max` to `vseb_head3_e1zero` — and the
split version satisfies all four. The fifteen does not move either: the two
new roundings cost a factor `(1 + u)` apiece and the constant comes out at
14.74 where the paper's came out at 14.

**What the constants did.**

| | paper | here | why |
|---|---|---|---|
| seed, `\|b sqrt x - 1\|` | 100u² | 104u² | three split lines, 8u² apiece at `u^2` |
| `ThreeProdDWn` (Alg 11) | 10.5u³ | 25u³ | Section 7.4's five refinement cases not ported |
| `ThreeProdOneTWn` (Alg 20) | 6u³ + (31c+10)u⁴ | 6u³ + (50c+30)u⁴ | only the `c u^4` side moves |
| **`ThreeSqRtNn`** | **24u³** | **31u³** | 25 halved twice, plus 6 |

The `25` is the one real loss, and it is deliberate. Section 7.4 exists to
keep the worst numerator away from the worst denominator, and every one of its
five cases would have to be re-proved with the extra roundings in — for a `d1`
that the square root then halves anyway. The naive bound is `22u^3` over
`1 - 4u`, which is 25 with room. The seed's `104u^2` is against a ceiling of
about 107 (`ThreeProdOneTW_error_c` takes its tolerance as a parameter no
larger than 112, and `sqrtAuxN_i2_near_1` delivers 108), so it fits with four
to spare.

**The bridge.** `twflx.v` matches the two developments operation by operation:
sums need nothing but finiteness (`dwflx.v` settled that), products need to be
clear of the bottom of the range, and the seed adds a square root, a division,
a halving and a Sterbenz subtraction. The result is `threeSqRt_X` — the
primitive floats compute `ThreeSqRtNn` — and then `threeSqRt_error`:

    |twval (threeSqRt x) - sqrt (twval x)| <= (31u^3 + 22500u^4) |sqrt (twval x)|

under one guard, `sqrt_ok`, which is the six guards of its parts at the
arguments the algorithm gives them.

**And the two bits.** `31u^3` is `31 * 2^-159`, which is `3.875 * 2^-156` — so
the measured `kscale = 2^-156` does **not** cover the proved bound, and
`2^-154` does, with three per cent to spare. `kscale_needed` in `twflx.v` is
the arithmetic. The probing measured 2.3 units of the last place and the proof
says 3.9, so the two are within a factor of two: the bits are the price of the
proof, not of the algorithm. Measured before the proof existed, at
`i_prec 107`, on the relative width of `interval_intro`'s own output:

| | at `2^-156` | at `2^-154` | |
|---|---|---|---|
| `PI` | 2^-154.2 | 2^-152.7 | +1.5 bits |
| `1/3` | 2^-155.0 | 2^-153.0 | +2.0 |
| `sqrt 2` | 2^-154.9 | 2^-153.0 | +1.9 |
| `exp 1` | 2^-150.2 | 2^-150.0 | +0.1 |
| a 25-digit rational | 2^-155.0 | 2^-153.0 | +2.0 |

Exactly two bits where the step is used and nothing where it is not — `exp 1`
is sums and products, which the step never touched — **and no time at all**:
the 150-bit pi bracket takes 0.56 s either way.

**What is still owed.** `sqrt_ok` itself. Discharging it from the hypotheses
`kstep_sqrt` is stated with needs the scaling: `sqrtTwUpP` and `sqrtTwDnP`
would take an even power of two out of the argument, run the algorithm in a
fixed binade and put half the exponent back, the way `dwsqrt.v`'s `sqrtDwUpK`
does. That is a change to the algorithm, not to a proof, so it is left as a
decision rather than made.

## Open

1. **Interval's 120-bit goal was refused, and `mag` was why.** The goal's
   whole content is a bound of half a unit in the last place, and Interval
   takes the size of that unit from `F.mag`. The first `mag` here was the
   largest of the three words with two binary steps added for safety, which
   is always **one bit too big** — so every ulp bound came out twice too
   large and the goal could not be proved at any precision. Measured at a
   point, `RND u - u` came out `±8.67e-19` where bignums give `±4.34e-19`,
   exactly twice, and the goal's bound is `65537·2^-77 = 4.34e-19`.

   `mag` is now the magnitude of the **value**: the three words added once
   upwards and once downwards, whichever is larger in absolute value. That
   agrees with `PrimitiveFloat.mag` exactly, and the goal goes through in
   0.174 s against bignums' 0.169. `code/ddouble` still has the loose
   version — its proof of `mag_correct` would have to be redone, and that
   format cannot reach this goal anyway.

2. **`method_error` is still refused, and that is not understood.** What has
   been ruled out, each by measurement:
   * *Not precision.* At a point this module encloses `f t - exp t` to
     `6.4e-47` where a double word gives `4.1e-30` and bignums `1.3e-31`.
   * *Not the Taylor model of a quotient*, the only thing `method_error` has
     that `poly_error` has not: both modules prove
     `Rabs (x/(1+x) - x*(1-x)) <= 3/10` under `i_bisect`/`i_taylor` in 70 ms.
   * *Not a margin.* The same goal is refused with the bound loosened twenty
     times over, to `1e-16`, while a bound of `1` is proved.
   * *Not `mag`* — tightening it fixed the 120-bit goal and left this one
     refused.
   * *Not `midpoint` or `wellFormed`.* Both are `real` on the values tried.
3. **Speed, and one goal where triple words lose.** `cancellation` is 174 s
   against 77.5 for bignums, 2.2 times slower, although every operation is
   quicker than the bignum one. The gap is per-call overhead bignums do not
   pay: every operation goes through `onReal2`, which runs `real` — a
   `classify` over three words and the two `wellFormed` comparisons — and
   the sum and the product allocate `seq` cells. On a goal that is a million
   cheap operations that overhead is the whole cost.

   Timed on their own, microseconds a call:

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
