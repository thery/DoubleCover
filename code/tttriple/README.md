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

**The quotient and the root assume nothing, and carry a guard instead.**
`div_UP_correct`, `div_DN_correct`, `sqrt_UP_correct` and `sqrt_DN_correct` are
proved. What they used to lean on was one measured number each, stated as
`Axiom kstep_div` and `Axiom kstep_sqrt` in `twpaper.v`; both axioms are gone.
In their place the step the answer is widened by is proved to cover what the
algorithm is out by, under a range condition the operation **evaluates** —
`div_okb` and `sqrt_okb`, whose every hypothesis is a boolean test on numbers
the algorithm has in hand. Where the test fails the quotient answers `nan`,
which Interval reads as the whole line; the root does better and scales the
number into the band. `probek.py`, which ran the two algorithms on forty
thousand random triple words and reported 2.3 units in the last place for the
quotient, is what the bound used to rest on and is now only a sanity check.

Everything between the guard and the obligation is proved: the guards
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
| pi by Machin, plain operations (`nearest/test_pi.v`) | right to **48.5 digits**, `2^-161` |
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
| `twarith.v` | the algorithms: the error-free transforms, the two sweeps, `vecSum` unrolled at six and fourteen, the second sweep fused with the cut (`expF`, and `expF3` at the length the widening uses), and `Merge` |
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
| `nearest/` | **off the build path**: the four operations rounded to nearest, the insertion sort the product used to do, and `test_pi.v`. Nothing calls them; they are what an obvious implementation looks like, and the gap between them and what runs is the argument for the paper's algorithms. See `nearest/README.md` |
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

Nothing here is on the build path. Build `code/ddouble` and then
`code/tttriple`, and run:

```
sh bench/run.sh                                  # one operation at a time
sh bench/run_goals.sh dw107 big107 tw159 big159  # the seven goals
```

Both generate one file a module from a template and run **each in its own
process**, which is the whole point of them: the two tables above were wrong
twice before they were right, once because every module ran in one process and
once because the loop let its accumulator drift. `bench/run_goals.sh` takes the
module names it should run, since `cancellation` alone is three minutes for
bignums at 159.

| | |
|---|---|
| `bench/ops_template.v` | one operation at a time, fixed same-size operands |
| `bench/goals_template.v` | the seven goals through Interval's tactic |
| `bench/cancel_probe.v` | the bound-and-depth sweep that shows `cancellation` is not a precision benchmark |
| `bench_ops.v` | the old all-in-one-process version; **it reads about 2.7x high** on whatever runs last and is kept only as the record of that mistake |
| `bench_bands.v` | the goals at the precision each **goal** asks for, rather than each format's own |
| `bench_prec.v` | the goals at each format's width, all modules in one file |
| `bench_lift.v` | the one goal in Interval's own sources that asks for more than a double word |

Interval's tactic decides which arithmetic runs by whether `i_prec` is given
at all (`src/Tactic.v:80`): **without** it the tactic uses primitive floats at
53 bits, hardwired, whatever module it was built on; **with** it, that module.
For the two word modules the number asked for changes nothing about the
arithmetic — `PtoP` throws it away — but it does tell the transcendental code
how many bits to aim for.

### One operation at a time

**How these are taken, because it matters.** `bench/run.sh` generates one file
a module from `bench/ops_template.v` and runs **each in a process of its own**,
twenty thousand operations a loop, the minimum of five, with an empty loop
subtracted from every row. Two mistakes are designed out of it, and both were
made here first:

* *All the modules in one process* — which is what `bench_ops.v` did, with
  triple words last — inflates whatever runs last by about 2.7x: the earlier
  loops fill the heap and the later ones pay the collections.
* *An accumulator that drifts.* A loop that computes `a := a + c` walks `a`
  away from `c`, so every step times exponent alignment as well as the
  operation. For bignums 40 binary places apart costs 2.5x what the same size
  does — 22.8 microseconds against 9.2 — while the word formats are flat. The
  two operands here are **fixed and the same size**, each with every bit of its
  mantissa used.

Microseconds an operation. Bignums appear at all three widths, so each word
format can be read against bignums at its own precision — the only fair
comparison — and against the others.

| op | floats 53 | bignums 53 | bignums 107 | **double words** | bignums 159 | **triple words** |
|---|---|---|---|---|---|---|
| add | <0.05 | 6.40 | 9.20 | **1.25** | 19.65 | **3.20** |
| sub | <0.05 | 5.55 | 7.50 | **1.00** | 12.25 | **3.30** |
| mul | <0.05 | 7.95 | 16.65 | **1.35** | 34.30 | **7.50** |
| div | <0.05 | 19.35 | 37.25 | **2.15** | 72.25 | **13.65** |
| sqrt | <0.05 | 19.70 | 43.30 | **2.70** | 83.40 | **14.95** |
| cmp | <0.05 | 1.65 | 2.20 | **0.35** | 2.85 | **1.15** |

A primitive float is below what this harness can resolve — the empty loop is
0.05 microseconds an iteration and every float row sits on it — so `<0.05` is
all that can honestly be said.

**Against bignums at its own precision**, a double word is 6.3x to 17.3x
quicker and a triple word 2.5x to 6.1x:

| | add | sub | mul | div | sqrt | cmp |
|---|---|---|---|---|---|---|
| double words vs bignums 107 | 7.4x | 7.5x | 12.3x | 17.3x | 16.0x | 6.3x |
| triple words vs bignums 159 | 6.1x | 3.7x | 4.6x | 5.3x | 5.6x | 2.5x |
| triple words vs double words | 2.6x | 3.3x | 5.6x | 6.3x | 5.5x | 3.3x |

**A triple word costs between two and a half and six times a double word**, and
the spread is the thing to read. The sum is 2.6x, which is about what one more
word should cost. The product is 5.6x and the quotient 6.3x, and that is not
waste: a double word's product uses **one** two-product and a triple word's
**four**, a quotient nine, and without an FMA each two-product is Dekker's
splitting, eighteen operations. Counted from the code, `divDwDw2` is 34
operations and `threeDiv` 298.

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

**And `vseb` is fused with the cut.** `vseb` over fourteen terms is thirteen
nested branches, so it cannot be unrolled at a fixed length the way `vecSum`
was. What can be done instead is to fuse it with the cut that follows: the cut
keeps the first two words the sweep emits and
adds everything below into the third, so a walk carrying an accumulator needs
no list at all — and it does not separate a second time either, because the
three words come out named. `expUp`'s right fold became a left fold, which is
what an accumulator can carry; the bound did not care, since every step rounds
the way the bound needs whatever order the terms come in.

`expF` in `twarith.v` is that walk, written once over an abstract `add` and
instantiated at `addUpFp` and `addDnFp`; `expF_eq` says it equals the cut as
the bounds are stated about it, so no proof in `twbound.v` looks at the
arrangement. Both sweeps needed their unfolding **stated** rather than
simplified — `simpl` takes `twoSum` apart as well, and then the two sides of
every equality stop looking alike.

Timed with both arrangements in one process, same inputs and same build, the
operation on its own and not through the module:

| | on lists | fused |
|---|---|---|
| `addTwUp` | 2.75 | **2.40** |
| `mulTwUp` | 7.2 | **6.15** |

**That is 1.15x, and the prototype said 1.6x.** The prototype skipped `vseb`
altogether, so it was measuring a ceiling: what fusing saves is the cons cells
and the second separation, not one two-sum of the arithmetic — the walk still
performs every one of them. Through the module the sum moves by less than the
noise and the product reads 7.7 against 8.0.

Where `method_error` is concerned it is worth more than that, because the
tactic pays the cut on every bisection: **4.9 seconds against 6.1**, and every
bracket still proves at the same precision.

**What is left.** The lists that are *handed in* are still lists: `Merge`
builds six cells for the sum and the product writes fourteen out. Feeding the
words in named would mean unrolling the walk at a fixed length, which is
thirty-two cases at six and eight thousand at fourteen. **It was tried at six
and it gains nothing** — see below.

### Every goal, at each format's own precision

`bench/run_goals.sh` runs all seven goals over one module in a **process of its
own**, asking bignums for the width each word format actually holds. That is
the fair question about the arithmetic; asking bignums only for what the goal
needs — `cancellation` asks for sixty bits and a triple word does a hundred and
fifty-nine on every call whatever is asked — flatters them, and is a different
question. Seconds; **refused** is Interval reporting *"Numerical evaluation
failed to conclude"*, a bound too wide for the goal, never a wrong answer.

| goal | bits it wants | bignums 107 | **double words** | bignums 159 | **triple words** |
|---|---|---|---|---|---|
| pi to 14 digits | 47 | 0.028 | **0.014** | 0.030 | 0.050 |
| pi to 24 digits | 82 | **0.011** | 0.016 | 0.014 | 0.016 |
| pi to 34 digits | 105 | refused | refused | 0.043 | **0.019** |
| pi to 45 digits | 150 | refused | refused | **0.020** | 0.036 |
| `method_error` | 80 | 6.07 | **1.56** | 9.52 | **4.46** |
| `poly_error` | 90 | 0.062 | **0.061** | 0.070 | 0.066 |
| `cancellation`† | 60 | 145.7 | **25.4** | 224.3 | **178.6** |

† `cancellation` measures bisection cost, not precision — see below. Primitive
floats do it in **0.21 seconds**, nine hundred times quicker than a triple
word, and no bound or depth makes it otherwise.

Four things to read off it.

**A double word is four to six times quicker than bignums wherever it
reaches** — `method_error` 1.56 against 6.07, `cancellation` 25.4 against
145.7 — and it reaches up to about a hundred bits.

**A triple word now beats bignums on every row it is compared with**, by 2.1x
on `method_error` and 1.26x on `cancellation`, and level on the brackets. It
was level overall before the clean-up and is ahead now.

**Only a triple word reaches the two tight brackets**, and it takes the
105-bit one more than twice as quickly as bignums do.

**`poly_error` separates nothing**, because at 90 bits every arithmetic here
has room to spare.

**`cancellation` IS NOT A PRECISION BENCHMARK, and should not be read as
one.** It is

```coq
Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. interval with (i_bisect x, i_depth 20, i_prec 60). Qed.
```

and it has **two** dials, the bound and the depth, neither of which is the
precision. What it evaluates at every node is `exp x - exp x` over a range, so
the width that comes back is the **dependency**: over `[0,1]` all three
arithmetics return `0x1.b7e151628aed3p+1`, which is `2(e-1)`, and over a node
of width `2^-20` at a half they all return `0x1.a612a61275772p-19`, which is
`2 sqrt(e) 2^-20`. The leading words agree bit for bit.

Only bisection narrows that, and **bisection costs `2^depth`** — measured, not
assumed: floats take 15.9 seconds at depth 24 and 145.3 at depth 27, a factor
of nine for three levels. Depth 27 is a hundred and thirty-four million splits.

So the bound and the depth are locked to each other and the arithmetic never
enters. Tightening the bound one decade costs three or four levels of depth and
an order of magnitude of time, for **every** arithmetic alike:

| bound | depth | floats 53 | |
|---|---|---|---|
| `1e-4` | 20 | ok | 0.19 s |
| `1e-5` | 20 | ok | 1.95 |
| `1e-6` | 20 | **refused** | 0.36 |
| `1e-6` | 24 | ok | 15.9 |
| `1e-7` | 24 | **refused** | 48.7 |
| `1e-7` | 27 | ok | 145.3 |

And precision buys **nothing**. At the bound and depth where floats give up,
so does everything else, all the way to two hundred bits:

| at `1e-6`, depth 20 | | |
|---|---|---|
| floats 53 | refused | 0.36 s |
| double words | refused | 44.8 |
| triple words | refused | 372.0 |
| bignums **200 bits** | refused | 495.2 |

To reach the point where a float's own rounding rather than the dependency is
the limit one needs a node of width about `2^-50`, which is depth fifty — a
thousand times more splits than depth forty would already make impossible. A
double word would need depth a hundred and a triple word a hundred and fifty.
**No setting of the two dials makes this goal test the arithmetic.**

What it does test is the cost of one cheap operation repeated a million times,
and there the fastest arithmetic wins outright. As the goal is actually
written, with `i_prec 60`:

| | seconds |
|---|---|
| primitive floats | **0.21** |
| double words | 25.9 |
| bignums at 60 bits | 81.6 |
| triple words | 188.9 |

A triple word is nine hundred times a float on a goal that needs none of it.
The row in the table above is kept because it is the standard benchmark, but it
measures per-operation cost and nothing else, and the bignum column in it is
bignums doing **two and a half times the work the goal asks for**.

**And `i_prec` is discarded by all three word formats.** `tw_ops.v` has
`PtoP (_ : positive) := tt` and `prec _ := 159`, so the number never reaches
the arithmetic and does not reach the transcendental code either. A word format
has one speed and no dial; only bignums have one. That is why every comparison
here has to name the width bignums were asked for — and why `cancellation` at
`i_prec 60` against `i_prec 159` reads 188.9 against 178.6 for triple words,
which is the same number twice.

One more thing worth noticing: bignums get **quicker** going from 107 bits to
159 on the pi brackets — at 107 they cannot reach the tight ones without
bisecting, at 159 they can.

And `cancellation` is the goal where primitive floats win outright: **3.80
seconds** at 53 bits, seven times a double word and forty-seven times a triple
word. Nothing about the goal needs more than a float, which is the point the
next paragraph makes.

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

### How many bits one operation pins down

The table above is a whole evaluation. This one is a single operation, which
is the thing to ask about the format itself: give both ends the same point,
apply the operation, and see how wide the answer is. **What is measured is
`I.add`, `I.mul`, `I.div` and `I.sqrt` — what coq-interval itself calls** —
and not the two directed operations read off by hand; on a point input the two
agree to the bit, which is what `Interval/Float.v:539` says they must
(`I.add prec (Ibnd x x) (Ibnd y y) = Ibnd (F.add_DN x y) (F.add_UP x y)`).

Bits of the answer the enclosure pins down, `mag(upper) - mag(upper - lower)`:

| op | double words | triple words |
|---|---|---|
| nominal | 107 | 159 |
| add | 104 | **159** |
| sub | 104 | **159** |
| mul | 103 | 157 |
| div | 101 | **152** |
| sqrt | 101 | **152** |

Steady over seven pairs of inputs. **The sum and the difference lose
nothing**: three words added and swept are exact, and the only thing that
rounds is the cut at the third word, which is one step — `2^-159` relative.
The product loses one or two, which is `pstep`. **The quotient and the root
lose seven**, and that is `kscale`, the step the answer is widened by, which
is `2^-153`; it is the algorithm's error bound and not the interface. The
interface costs the one bit that any two-sided enclosure costs — bignums at
159 read 158 for the same reason.

**And past a point none of it matters.** Widen the input to a relative width
of `2^-k` and ask what comes out:

| input width | triple: mul | div | sqrt |
|---|---|---|---|
| `2^-160` (a point) | 156 | 152 | 152 |
| `2^-150` | 149 | 149 | 150 |
| `2^-140` | 139 | 139 | 140 |
| `2^-100` | 99 | 99 | 100 |
| `2^-40` | 39 | 39 | 40 |

Once the input is wider than about `2^-150` **the operation adds nothing at
all**: the answer has the bits the input had, and the root gains one because
it halves the relative width. A double word does the same thing at `2^-100`.

So the extra word buys **reach** — 152 to 159 bits held where a double word
holds 101 to 104 — and it buys nothing whatever on a goal whose intervals have
already opened up. `cancellation` is that goal: its width is the dependency,
so all three arithmetics return the same interval and the extra word is paid
for and not used.

### The walk unrolled at six, which gains nothing

`vecSum6` builds a six-word list and the fused walk traverses it, so the walk
looked like the next thing to write out at a fixed length. It was generated
rather than written by hand — `Eval cbv` over the walk's own constants, leaving
`twoSum` folded, so the answer is `expF`'s by construction and the equation is
`by []`.

Generated **with** `zeta` it is **three times slower**: stripping the `let`s
duplicates every shared two-sum and the evaluator recomputes them. That is
worth knowing on its own, and it is why `expF3` for the widening was written by
hand with its sharing kept.

Generated **without** `zeta` it is level with the list version — 0.059
microseconds against 0.062, which is noise. So the traversal was never the
cost: what a six-cell list costs to build and walk is below what can be
measured here, and the arithmetic is the whole of it. The walk stays as it is.

### `Merge` was tried and put back

The product stopped sorting its fourteen terms for nothing — the sweeps are
exact whatever order they are given and the bound only asks that the sum is
unchanged. The sum has the same shape, `Merge` over six terms, so the same cut
was tried: write them `x0 y0 x1 y1 x2 y2` and drop the merge.

The arithmetic says it is nearly free. Over random pairs, checked exactly in
`Z`, every answer is still well formed and still a true enclosure, and the
worst enclosure is **the same to the bit** at equal size and at `2^-30` and
`2^-60` apart — one bit wider, 157 against 158, only at `2^-110`. And the sum
goes **2.40 microseconds to 2.00**.

**The goals say otherwise.** That one bit costs the two that bisect about
eighteen per cent each:

| | merged | written in order |
|---|---|---|
| `poly_error` | **0.086** | 0.107 |
| `method_error` | **4.67** | 5.74 |

So the sum is 17 per cent quicker and the goals are 18 per cent slower, which
is the wrong way round. `Merge` is back.

**Why the product could and the sum cannot.** The product's fourteen terms have
sizes that are known in advance — they are the nine products of two triples,
and which is bigger than which does not depend on the values. The sum's six do
not: they come from two separated triples whose relative magnitude is whatever
the caller passes, so `y0` can land anywhere from above `x0` to below `x2`, and
only a comparison can say where. Sorting is doing real work there and nothing
in the term order can replace it.

### A cheaper addition was tried, and it costs reach

The sum is the operation furthest from what one more word ought to cost: a
double word's `addDwUp` is three two-sums and a shortcut, a triple word's is
about twelve plus three lists, because it does not use the fact that both its
arguments are **already separated triple words**. It merges six arbitrary
terms and renormalises from scratch.

So a specialised one was written and measured: pair the terms by position,
leading with leading, middle with middle, last with last, carry what falls out
of each pair down to the next, and renormalise the three words that are left.
Five two-sums and three directed adds, no list at all.

It is sound. Over forty thousand random pairs, checked exactly in `Z`: every
answer is `wellFormed`, every upper end is at or above the exact sum and every
lower end at or below it. And it is quick — `addTwUp` 2.55 microseconds to
**0.65**, which is 3.9x, and 1.86x a double word's 0.35, which is about what
one more word should cost.

**It still cannot be used, because it loses `poly_error`.** The four brackets
on pi all prove, the 150-bit one included; `poly_error` is refused.

The reason is worth writing down. Worst enclosure over four thousand pairs,
bits, with the second argument scaled down so its leading word lines up
further and further below the first's:

| second argument | paired | general |
|---|---|---|
| same size | **154** | 159 |
| `2^-30` down | 157 | 157 |
| `2^-60` down | 157 | 158 |
| `2^-90` down | 158 | 158 |

The loss is worst when the two are the **same** size, and gone when they are
far apart — so it is not the pairing, it is cancellation in the leading pair.
**The general route rounds at the answer's last word; the paired route rounds
at the arguments' last word**, and when the leading words cancel those are not
the same place at all. Sweeping the tail exactly first, two two-sums more, does
not help: it reads 152, slightly worse.

That is what the renormalisation is for, and it is why the sum cannot simply be
shortened. What would work is a test on the leading exponents, taking the
paired route when they are far enough apart that nothing can cancel and the
general one otherwise — but that is two algorithms to prove instead of one.

One thing the prototype did catch, and it is the bug this file already
records once: `addUpFp 0 0` is `next_up 0`, the smallest float there is. Since
`fromZ 1` is `TWFloat 1 0 0`, **every whole number the tactic makes** came back
with a subnormal second word a thousand bits below its first, the quotient's
guard refused it, and the very first bracket on pi failed. `addUp0` leaves a
sum of two noughts alone, exactly as `mulUp0` does for a product.

### The guard inside the computation, and what is left of it

The rule is that a guard must not be a second pass: whatever it tests, the
algorithm has already computed, and it should be handed over rather than
worked out again. Checked across every file, by matching each `X` against its
`X_okb`:

| | |
|---|---|
| `reciBWG`, `sqrtBWG` | answer and flag in one pass, every term shared |
| `prodDWG`, `prodOneG` | the same; `m11` and `m02` named and used twice |
| `threeDivG`, `threeSqRtG` | one pass, and they hand the flag up |
| `mulFv` | reads the product in hand, where `mulF` asked for `a * b` again |
| `sub2Tw_okb`, `sub32Tw_okb`, `halfTw_okb` | test the **input**, not a recomputed output |
| `subOkb`, `fastTwoSumOkb` | share through `let` |
| `div_okb`, `sqrt_okb` | second passes by design — they are the specification, and nothing calls them |

Two places were still doing work twice. Both are real and both measure at
almost nothing, which is the point of writing them down.

**`halfOkb` did the division four times a word, and now does it once.** It was
`finF (a / 2) && finF ((a / 2) * 2) && ((a / 2) * 2 =? a)` — three halvings and
two doublings — and `threeSqRtG` computes `halfTw bw` beside it, so each of the
three words was halved four times over. `halfOkbv a h` now takes the half the
algorithm already has and `halfTw_okbv t u` the triple of them, with
`halfOkb a := halfOkbv a (a / 2)` and `halfTw_okb t := halfTw_okbv t (halfTw t)`
so that the old statement is the new one at that argument. **No proof needed
changing** — `half_exact` and `halfTw_okbP` read exactly as they did, and
`threeSqRtGE` still closes by conversion. Measured on the expression itself,
`halfTw bw` beside its test goes **0.80 microseconds to 0.70**; in a root of
fourteen that is under one per cent, which is why it is worth having only
because it cost nothing.

**The outer guard reads `abs (tw0 q)` three times**, and `kstep` inside
`shiftUp` reads it twice more and recomputes `kscale * abs (tw0 q)`. Sharing
all of it and passing the step straight to `widenUp` times **the same**: the
guard's pieces are each at the noise floor — `magDnTw` 0.4 µs, the four
`normF` tests 0.6, `wellFormed q` 0.2, the three `abs`/`finF` tests 0.2.

So the quotient's fourteen microseconds are 10.6 algorithm, 2.2 guard, 1.2
shift, and there is nothing left in the guard worth a proof.

**The shift had one thing left in it.** `widenUp` cuts a list of exactly three
words, and `expF` walked it as a list like any other. At three the walk is two
nested tests and four cases, and since nothing is ever folded there it needs no
`add` at all — `expF3` in `twarith.v`, with `expF3_eq` for the proofs. The
widening reads **0.85 microseconds against 0.50**, and every quotient and every
root goes through it once: `divTwUpQ` 12.4 to 11.8. All six goals still prove.

What is left after that is the algorithm.

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
   proves in 4.9 s.
3. **Speed: the lists that are handed in.** Both sweeps are off `seq` now —
   `vecSum` is unrolled at the two lengths it is used at and `vseb` is fused
   with the cut into one walk — and what is left is the list each operation
   *builds* before any sweep runs: `Merge`'s six cells for the sum, the
   product's fourteen written out. Feeding the words in named means unrolling
   the fused walk at a fixed length. It was tried at six and gains nothing:
   the list the walk traverses was never the cost.

   Timed on their own, microseconds a call, five thousand a loop:

   | | µs |
   |---|---|
   | `plusTwTw`, rounded to nearest | 2.8 |
   | `timesTwTw`, rounded to nearest | 8.4 |
   | `mulTwUp` | 6.2 |
   | `divTwTw`, three rounds of long division | 25 |
   | `sqrtTw`, two Newton steps | 49 |
   | `divTwUpQ`, the paper's Algorithm 14 | 14.0 |
   | `sqrtTwUpP`, the paper's Algorithm 15 | 14.0 |

   The first two are the seeds, and **they are not what the format uses**:
   `tw_ops.v` takes the quotient and the root from Algorithms 14 and 15. An
   earlier version of this table quoted 98 and 408 microseconds for
   `divTwUp` and `sqrtTwUp`, the residual-bound route. Those were **dead
   code** — nothing called them — and quoting them here was measuring
   something the format does not run. They have been deleted.

   Where the quotient's fourteen microseconds go, measured the same way:

   | | µs |
   |---|---|
   | `threeDivG`, the algorithm and its flag | 10.6 |
   | the guard's remaining tests | 2.2 |
   | `shiftUp`, the widening | 1.2 |

   So the algorithm is three quarters of it and there is no large saving left
   in the wrapper. Sharing `abs (tw0 q)`, which the guard computes three times
   and `kstep` twice more, is worth 0.2 µs — one and a half per cent, and not
   worth the proof it would need.

