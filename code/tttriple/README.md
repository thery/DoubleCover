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
proved**; nothing in it is `Admitted`. **And nothing is assumed**:
`Print Assumptions` on any obligation — the quotient and the root included —
names only Rocq's own primitive-float axioms and classical reals. Both leant
on one measured number until they were proved; see *The root* and
*The quotient* below.

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

## And a second trap: a step that is not a word

The product is widened by a fixed step, `teps = 2^-1070`, and that step is
enough for the bound: of the nine products in the expansion the four that
carry the value are taken by a two-product, which can only miss by three and
a half of the smallest float there is, and the five that are smaller are
rounded the way the bound wants. Nothing has to be estimated.

But `2^-1070` beside a leading word of six **is not a word of the answer**.
It is a subnormal a thousand bits below where a third word belongs, and every
*exact* product picks one up: `2 * 3` came back as

```
TWFloat 6 0x0.0000000000015p-1022 0
```

Such a triple word can never be divided by. The quotient needs `a * x1` with
`a` about one over `x0`, and with `x1` that far under `x0` the product falls
below the line where the paper's bounds hold, so the guard refuses it. Scaling
does not help either: `x1 / x0` does not move. So `mul` then `div` gave `nan`,
and Interval's exponential does exactly that — which is what made `exp x <= 3`
fail over `[0,1]` while `exp 1` on its own was fine.

The step is now taken at the last word's own place: `pstep w` is the larger of
`teps` and `2^-159` of the leading product, which is about one step of a third
word and so costs nothing, and only the `teps` part is what the bound uses.
The five small products got the same treatment — rounding upwards takes nought
to the smallest float there is, and five of those make another word that is
not a word of the answer, so `mulUp0` leaves an exact nought alone. `2 * 3` is
now `TWFloat 6 0x1.8000000000001p-157 0`, and dividing by it works.

## The files

| file | what it holds |
|---|---|
| `twarith.v` | the algorithms: the error-free transforms, the two sweeps, `sortMag`, `Merge`, and the operations rounded to nearest |
| `tw_updn.v` | the directed operations: the widening steps and the up and down forms of each |
| `tw_ops.v` | the interface: `TwFloat`, its obligations, and the sealing |
| `twpaper.v` | the paper's algorithms on primitive floats: Algorithms 9, 11, 14, 15, 18, 20, and the step |
| `twprodg.v` | Section 6.2 of the paper, made generic in `c` and `z3`, and Algorithm 9 without the fused multiply-add |
| `twseed.v` | the seed, the two products and the root, all with nothing fused: `ThreeSqRtNn_error` |
| `twflx.v` | the bridge, primitive floats to the paper's reals, ending in `threeSqRt_error` and `kstep_sqrt_testable` |
| `twdivn.v` | the quotient's seed and Algorithm 14, both without the fused lines: `ThreeDivN_error` |
| `twdivflx.v` | the quotient's bridge, ending in `threeDiv_error` and `kstep_div_testable` |
| `twdiv.v` | the quotient behind its guard: `divTwUpQ`, `divTwDnQ` and their two bounds |
| `twsqrt.v` | the root behind its guard and its scaling: `sqrtTwUpK`, `sqrtTwDnK` and their two bounds |
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
coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith bench_prec.v
coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith bench_lift.v
```

`bench_ops.v` times the arithmetic with no tactic above it; `bench_bands.v`
times Interval's tactic over each arithmetic, at the precision each goal asks
for; `bench_prec.v` does the same at the precision each format holds;
`bench_lift.v` is the one goal in Interval's own sources that asks for more
than a double word.

Interval's tactic decides which arithmetic runs by whether `i_prec` is given
at all (`src/Tactic.v:80`): **without** it the tactic uses primitive floats at
53 bits, hardwired, whatever module it was built on; **with** it, that module.
For the two word modules the number asked for changes nothing about the
arithmetic — `PtoP` throws it away — but it does tell the transcendental code
how many bits to aim for.

### One operation at a time

**How these are taken, because it matters.** Each module is timed in a
process of its own, two thousand operations a loop, the minimum of eight
loops. Running all four modules in one process — which is what `bench_ops.v`
does, with triple words last — inflates the triple-word rows by about 2.7x:
the bignum loops fill the heap and the triple-word loop pays the collections.
That mistake is what made an earlier version of this table read 0.118 for an
addition that costs 0.042.

Microseconds an operation. Bignums are asked for the precision each word
module actually holds, so this is a comparison at equal precision.

| op | bignums 159 | double words | triple words | triple, before |
|---|---|---|---|---|
| add | 18.0 | **0.5** | 3.5 | 4.0 |
| mul | 28.0 | **1.0** | 8.0 | 11.5 |
| div | 56.5 | **1.5** | 14.5 | 35.7 |
| sqrt | 55.5 | **2.5** | 15.0 | 37.0 |

**A triple word beats bignums at its own precision on all four**, by 3.7x to
4.5x. Against a double word it costs 6x on the root, 8x on the sum, 10x on the
quotient and 11x on the product.

**Why it is not 2x.** The obvious sum — nine products against four — is the
wrong count. A double word's product uses **one** two-product and finishes
with a `fastTwoSum`; a triple word's uses **four**, and a quotient nine, and
without an FMA each two-product is Dekker's splitting, eighteen operations.
Counted from the code, `divDwDw2` is 34 operations with one two-product and
`threeDiv` is 298 with nine — 8.8x, which is what the table shows now that
the guard has been fixed.

**Two things were wrong, and both were mine.**

*The guard was a second pass.* It recomputed the whole algorithm, and every
`mulF` recomputed the product the algorithm had just made, and it tested
twenty-one intermediates for being a number. `code/ddouble`'s guard is
eleven operations and tests no intermediate at all: one range test a product,
and finiteness by the argument `twoProd_err` already rests on — each number
is an argument of the operation that made the next, so the last one being a
number proves they all were. The triple-word guards are now that shape:
`mulFv` reads the product in hand, `twoProd_finI` carries the finiteness, and
what is tested is one range fact a product plus the last word. That took the
quotient from 35.7 to 14.5 and the root from 37 to 15.

*The sweeps were written on `seq float`.* `vecSum` and `vseb` are how the
paper reads, and they allocate a cell a word and are walked by an
interpreter: 44 to 73 nanoseconds an operation against a double word's 16.
On a fixed size they unroll into named words — over the quotient's **four**
tail terms `vseb` is four branches — and `prodDWF_eq` says the answer is the
one the bounds were proved about. Algorithm 11 went from 4.4 microseconds to
1.4, Algorithm 14 from 11.0 to 4.1.

For the sum and the product only part of that is done. `vecSum` is unrolled
at both lengths they use, six and fourteen (`vecSum6_eq`, `vecSum14_eq`,
proved by computation since the chain has no branch), and the product no
longer sorts its fourteen terms: they are written in the order their sizes
are known to be in, and the bound never uses the order — only that the sum is
unchanged. That is mul 11.5 to 8.0 and add 4.0 to 3.5, and it costs nothing
in reach: the 105- and 150-bit brackets still prove.

**What is left, and what it is worth.** `vseb` over fourteen terms is
thirteen nested branches, so it cannot be unrolled the way the quotient's
was. The way to do it is to fuse it with the fold that follows: make
`expUp`'s right fold a left fold, so a producer can carry an accumulator,
then walk `vsebAux` once emitting two words and accumulating the rest, with
no list at all. Measured on a prototype that skips `vseb` entirely — an upper
bound on what is achievable, not an implementation — the sum would go to
about 2 microseconds and the product to about 5. That is 1.6x, and it is not
done.

### Every goal at the same precision

`bench_bands.v` asks bignums for the precision each **goal** needs. That is the
fair question if one is buying a proof, and not the fair question about the
arithmetic: `cancellation` asks for sixty bits and a triple word does a
hundred and fifty-nine on every call whatever is asked. `bench_prec.v` pins
bignums at each word format's own width and runs all seven goals at both.

At 107 bits, which is what a double word holds:

| goal | bignums 107 | double words |
|---|---|---|
| pi to 14 digits | 0.029 | **0.012** |
| pi to 24 digits | 0.074 | **0.015** |
| pi to 34 digits | refused | refused |
| pi to 45 digits | refused | refused |
| `method_error` | 4.95 | **1.16** |
| `poly_error` | 0.056 | **0.047** |
| `cancellation` | 127.9 | **22.6** |

At 159 bits, which is what a triple word holds:

| goal | bignums 159 | triple words |
|---|---|---|
| pi to 14 digits | **0.018** | 0.020 |
| pi to 24 digits | **0.013** | 0.016 |
| pi to 34 digits | **0.015** | 0.019 |
| pi to 45 digits | **0.019** | 0.047 |
| `method_error` | 8.54 | **6.09** |
| `poly_error` | **0.066** | 0.075 |
| `cancellation` | 220.9 | **229.1** |

**A double word is two to six times quicker than bignums wherever it reaches.
A triple word is level with them**: quicker on `method_error`, level on
`cancellation`, within noise on the four brackets. That is the honest
reading, and it is a different one from the table above, where bignums are
asked for less work than they are being compared against.

Each figure is taken in a process of its own. Making the quotient and the
root twice as quick moved `cancellation` from 282.7 to 229.1, and did **not**
move `I.exp`, which is 6.2 milliseconds either way: **the exponential is not
quotient-bound, it is product-bound**, and the product is the operation still
written on lists. A product is 2.5 microseconds of arithmetic against 8.5 of
list machinery — 3 of them `sortMag` over fourteen terms, 2.5 `vecSum`, 3
`vseb` and the cut. That is the next thing worth doing, and it is the one
that would move this row.

One more thing worth noticing: bignums get **quicker** going from 107 bits to
159 on the pi brackets — at 107 they cannot reach the tight ones without
bisecting, at 159 they can.

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

**And the bits.** `31u^3` is `31 * 2^-159`, which is `3.875 * 2^-156` — so
the measured `kscale = 2^-156` does **not** cover the proved bound. The
quotient's `56u^3` is 7 of those units, which is what settles the constant:
`kscale = 2^-153`, three bits above the measurement and one above what the
root alone would need. `kscale_needed` in `twflx.v` is
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

**And the guard is a test.** `sqrt_ok` is a conjunction of two kinds of
clause: a word being a number, and a value being clear of a line. Both are
testable — the first because a number less itself is nought and nothing else
is, the second because rounding is monotone and the line is a float, so a
rounded value above the line has its exact value above it too. That is what
`code/ddouble`'s `divOk` and `sqrtOk` do, and `sqrt_okb` does it clause for
clause for all six guards of Algorithm 15's parts. Two clauses were not about
a line at all and had to be restated as what they really were:

- **halving**, which `halfTw` does to all three words and the seed's third is
  nought — the clause wanted is the halving being *exact*, and a word that
  comes back when doubled is a word whose halving lost nothing;
- **`3/2 - x0`**, where at the call site `x0` is exactly a half and Sterbenz
  does not apply, although the subtraction is exact. The two-sum settles it
  in general: its two words add up to the exact sum, so a zero low word is
  the high word being it.

A third came from the products: a triple word read off an integer has two
zero words, and a product that is nought needs no line, both formats
rounding it to nought. Flocq's `Dekker` already takes that disjunction.

So `kstep_sqrt_testable` is the axiom with **every hypothesis a boolean the
program can evaluate**, and `Print Assumptions` on it names nothing of ours.
`sqrt_okb` comes out true on 1, 2, pi to a hundred and sixty bits, `2^-1060`
and `2^-1000`, and false near the top of the range, where Dekker's own
splitting overflows.

**And the operation tests it.** `twsqrt.v` takes `sqrtTwUpP` and `sqrtTwDnP`
out of `twpaper.v` and puts them behind that test; where it fails the answer
is `nan`, which an interval library reads as no information and is always
sound. `Axiom kstep_sqrt` is gone. `sqrt 2` and `sqrt (3 + eps)` bracket as
before and all four pi brackets still pass.

**And where it fails, the number is moved into the band.** `sqrtOkT` holds
for a leading word from about `2^-969` up to about `2^996`, and the two ends
fail for different reasons: at the top Dekker's splitting takes a word up by
`2^27 + 1` and reaches infinity just below `2^997`; at the bottom the step is
a proportion of the leading word and the second word sits 53 bits below the
first. **One scale serves both ways**, and it is `2^160` — the failing bottom
lands in `[2^-914, 2^-809]`, the failing top in `[2^835, 2^864)`, both well
inside. 160 is even, which is what lets the answer come back by half of it.
Scaling up is exact and needs no test; scaling down is tested, by scaling
back. Behind all three paths is still `nan`, so the operation is total.
`sqrt 0x1p+1000` and `sqrt 0x1p-1060` now bracket where they gave nothing.

## The quotient

Algorithm 14 is the reciprocal's Newton double word and **three products**,
and the three products were already done for the root. What was left is the
seed, whose five lines the paper writes with two fused multiply-adds:

| | paper | here |
|---|---|---|
| `h1 <- RN(-h11 - a x1)` | 3u² | 6u² |
| `b12 <- RN(b11 + a h1)` | 4u² | 7u² |
| the Newton step, against `a` | 7u² | 13u² |
| `\|b x - 1\|` | 34u² + 123u³ | **40u² + 200u³** |
| **`ThreeDivN`** | 29u³ | **56u³ + 5000u⁴** |

The square of the starting error does not move — it is `a` alone, which is
unchanged — so all six of the extra `u²` are the seed's. The paper writes its
own `34` and `35` into `sub2_near_one`, `newton_sq_le` and
`div_error_assembly`; ours is `40`, so the three are restated with it and the
assembly's 71, 107 and 1165 become 83, 90 and 1700.

Twenty-five of the fifty-six is each of the two double-word products, which
the quotient does **not** halve — unlike the root, which does — and six is
Algorithm 20, unchanged.

**The `h11` line is where the machine and the paper part company in shape and
meet in value.** The paper writes one fused `RN(a x0 - (1 + 2u))`; the machine
takes the two-product's low word round the houses, `(p - (1 + 2u)) + e`. They
agree because `p` **is** `1 + 2u` — that is what tilting `a` by it was for —
so the subtraction is nought and what is left is `e`, which is the fused
line's value.

The guard is `div_okb`, the same two kinds of clause as the root's, and
`twdiv.v` puts `divTwUpQ`/`divTwDnQ` behind it. `Axiom kstep_div` is gone.

**What could still be done.** Where the quotient's guard fails the operation
gives up. Scaling would work here too — `z/x` scales by `2^(a-b)` when `z` and
`x` scale by `2^a` and `2^b`, so both can be normalised independently and the
answer corrected — but unlike the root it needs two scalings and a subtraction
of exponents, and it is not done.

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

2. **`method_error` was refused, and it was the midpoint.** It was `midpoint`
   and `wellFormed` after all — an earlier note here said it was not, on too
   few values tried. `midpoint x y` was `div2 (plusTwTw x y)`, and `plusTwTw`
   adds to nearest but does not sweep, so its three words can overlap: a third
   and a third come back as `0x1.5555555555556p-1` beside
   `-0x1.5555555555555p-54`, and two thirds of a step of the leading word is
   more than half of one, so `wellFormed` is false and the whole triple reads
   as nothing. Interval then has no point to halve its range at and every goal
   that bisects is refused — which is why `poly_error` and `cancellation` went
   the same way whenever they were asked to bisect.

   The midpoint is now the half of the sum that *does* sweep, `addTwUp`, held
   between the two ends by `min` and `max`: a bound rounded outwards can leave
   the range it was cut from, and then the end is the answer. `method_error`
   proves in 6.4 s.
3. **Speed: the sum and the product are still on lists.** `cancellation` is
   229 s against 221 for bignums **at the same 159 bits** — level. At the
   sixty bits the goal asks for, bignums take 76.7, and that is the number to
   quote only if one is willing to compare a tenth of the work with the whole
   of it. What is left is the product: 2.5 microseconds of arithmetic against
   8.5 of `sortMag`, `vecSum`, `vseb` and the cut, all allocating `seq` cells
   at 44 to 73 nanoseconds an operation where a double word's straight-line
   code runs at 16. The quotient and the root are off the lists;
   `prodDWF_eq` shows how — unroll the sweep for the fixed size and prove
   the answer is the same. The sum and the product have not been done.

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
