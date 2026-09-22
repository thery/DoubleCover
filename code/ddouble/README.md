# Double words on primitive floats

A **double word** is a pair of binary64 floats `DWFloat xh xl` standing for the
real number `xh + xl`. Two words hold about 32 decimal digits where one holds
16.

Rocq already gives primitive floats an interface — the operations and the
theorems that say what they compute. The goal here is an interface of the same
kind for double words, so that a proof can be carried out over them instead.
`dw_ops.v` is that interface.

## Building

The project builds on the `native` switch (Rocq 9.1.1), which is also the one
the Rocq server uses. `coq-interval` and `coq-flocq` must be installed there.

```
make
```

The `Makefile` comes from `_CoqProject` by `coq_makefile`; add any new file to
`_CoqProject`.

## The shape of the interface

`dw_ops.v` builds a module `DwFloat` matching Interval's `FloatOps` signature:
`add_UP`, `add_DN`, `mul_UP`, … together with `classify`, `cmp`, `neg`, `abs`
and the rest. That signature was chosen for one reason: **its obligations are
inequalities**, `le_upper` and `le_lower`.

That matters, because a double word is not a floating-point format. Its
addition and multiplication are not correctly rounded to 107 bits, so there is
no equation of the form `DW2SF (add x y) = SFadd 107 …` to be had, and none is
promised. Every statement here is a bound.

A pair that is not a well-formed double word, and any answer that ran out of
range, is read as `Xnan` — the whole line. That is always a valid bound. It
just says nothing.

## What is proved

| operation | algorithm | bound |
|---|---|---|
| `add_UP` / `add_DN` | `addDwUp` / `addDwDn` | proved |
| `sub_UP` / `sub_DN` | the sum with the second word negated | proved |
| `mul_UP` / `mul_DN` | `mulDwUp` / `mulDwDn` | proved |
| `div_UP` / `div_DN` | `divDwUpK` / `divDwDnK` | proved |
| `sqrt_UP` / `sqrt_DN` | `sqrtDwUpK` / `sqrtDwDnK` | proved |

A whole number enters as two words as well. `fromZ_UP` and `fromZ_DN` split it
into its top fifty-three bits — a whole number times a power of two, and both
of those are floats exactly — and what is left. The two-product multiplies the
two factors and reports its own error, and the test that the error is nought is
the whole proof that the product is the top part. A number one float already
holds is left alone, and is exact; a number past about `2^105` falls back to the
one-word answer, since the power of two would no longer be a float.

What the two-product may have left is then covered by a step of `deps`, which
is four of the smallest number there is — the honest size of the thing, since
the two-product can miss by three and a half of them.

```coq
Compute fromZ_UP tt 314159265358979323846264338327.
  = DWFloat 0x1.fb8d3a0e37652p+97 (-0x1.596ddc090d1fcp+43)
```

The two bounds come out about `2^-104` apart instead of the `2^-53` a single
float gives.

**This cost twenty-three bits until it was measured.** The step used to be
`+1` on the whole number left over — the smallest step available if the
widening has to stay in the integers, and it does cover the two-product. But
one is an *absolute* step, so on a constant of twenty-five digits it is
`2^-80` in relative terms, not `2^-106`. Measured through Interval, the
enclosure of `3141592653589793238462643 / 10^24` came out `2^-78.3` wide
where every other operation of this module gives `2^-100` or better, and a
goal asking for eighty-two bits was refused on its own constants before the
arithmetic was ever reached. With `deps` it is `2^-101.1`, level with the
rest, and that goal passes. The lesson is the general one: a bound that is
correct can still be the thing that decides whether a tactic concludes, and
only a measurement tells you which bound that is.

**Four operations are bounded by a shift, not by a residual.** `div_UP`,
`div_DN`, `sqrt_UP` and `sqrt_DN` are bounded by a shift of sixteen units in
the last place. All four are proved. **The development is admit-free**, and its
assumptions are the primitive-float and primitive-integer axioms and the
classical reals, nothing else.

**Sixteen is the paper's own constant.** `DWDivDW.v` holds Theorem 7.1,
admit-free, for `DWDivDW2` — which is `divDwDw2` of `dwarith.v` step for step:

```coq
Rabs ((zh + zl - xy) / xy) <= 15*u^2 + 56 * u^3
```

That is fifteen units in the last place of the low word, and sixteen is the
next power of two above it, so the shift is an exact exponent change.
Probing the same algorithm on 200000 random double words (`c/probek.py`) gives
5.82 units worst case, well inside it.

**That theorem now reaches the program.** It is stated over the reals in the
format with no smallest exponent, while the code runs primitive floats in the
bounded one, and `dwdivflx.v` is the road between the two — what `dwflx.v` is
for the sum. Its `divDwDw2_relerr` is the bound above, said of `divDwDw2` on
primitive floats:

```coq
Rabs ((zh + zl - xy) / xy) <= 15 * Du ^ 2 + 56 * Du ^ 3
```

It asks two things: that the arguments really are double words, and that the
guard holds — every step of the algorithm a number, and the product and the
two quotients out of the subnormal range, which is where the two formats round
alike. The sum needed no such range test, since a sum too small for the bounded
format to round is exact and so neither format rounds it. A product and a
quotient have no such property, and that is the whole of why the quotient is
the harder of the two.

**And so `div_UP` and `div_DN` are proved.** Three things had to be settled
besides the theorem itself.

*The step is taken from both words of the answer.* The paper's bound is
relative to the exact quotient, so something computed has to stand for the
quotient. The two words added in absolute value do, whatever the low word is.
The high word alone would need the answer to be a double word — `zl` no larger
than `u` times `zh` — and that is a further theorem, which the paper does not
leave and which Fast2Sum does not give without its own precondition on the last
call. `divDwDw2_step` is the arithmetic: `15u² + 56u³` against `16u²`, a
sixteenth over, and a sixteenth is far more than the `u` the reading costs.

*The range is tested as the division goes.* `divDwDw2G` computes the quotient
and looks at its own four intermediates on the way; computing them again for a
separate test would cost as much as the division. Measured on 200000 divisions,
twice each: the quotient alone 0.22 seconds, the quotient with its guard and its
shift 0.29, the quotient with its residual 2.15. The guard and the shift
together cost a third over the bare division, where the residual costs ten
times it. Two of the four tests have an escape for nought, and must: the low
word of a double word is often nought, and then `yl·t` is nought, which no
magnitude test can pass; a division that comes out exact leaves `d` nought, and
the same again. Both formats round nought to nought, so nought serves as well
as being normal.

*Nought divided is nought.* No magnitude test can pass on a nought numerator,
and an interval with nought for an endpoint is not a rare thing, so that case
is answered directly and exactly rather than refused.

When the guard does fail the operation answers `Xnan` — the whole line, which
is always a valid bound and says nothing. In the range where the arithmetic is
worth using it does not fail.

## The root, which had no theorem to carry down

The ported development says nothing about `sqrtDw`, so unlike the sum and the
quotient the root is not a theorem carried down but one proved here, in
`dwsqrt.v`.

**One step of Newton's method suffices because the step is quadratic.**
`sqrtDw` takes the machine root of the two words added as its guess, divides
the double word by it, adds the two and halves. The guess is within `2u` of the
true root — two roundings, the two words into one and the root of that. Newton
squares that:

```
(S - R)^2 / (2 S)
```

so four squared roundoffs over two, two and a half once the divisor is allowed
to be a little small. The quotient of the number by the guess contributes half
of its own error, eight, and the sum of the two all of its, four. **Fourteen
and a half against the sixteen of the shift**, which is the margin the whole
thing turns on.

It leans on everything above it: `divDwDw2_err` for the quotient,
`plusDwDw_relerr` for the sum, and `divDwDw2_dw` for the quotient being a
double word — which the sum asks of its arguments, and which is Fast2Sum's
precondition on the division's last call, tested by `divDwOk`.

**The halving is not exact, and the operation tests it.** A word whose last
digit is the smallest there is loses that digit when halved. Rather than argue
about where the bottom of the range is, `halfOk` tests it: doubling is always
exact, so a word that comes back from its half doubled is a word whose half was
exact.

**The guard shares its work, as the division's does.** Read plainly, `sqrtOk`
works the division out three times over — once for `divOk`, once for
`divDwOk` and once inside the sum it halves — and `sqrtDw` works it out a
fourth. `sqrtDwG` does the step once and hands back the answer with its four
tests beside it, and `divDwDw2GS` is `divDwDw2G` with Fast2Sum's own
precondition tested as well, since it is read off the same two numbers.
Measured on 100000 roots, three runs each, seconds:

| | before | now |
|---|---|---|
| the root alone | 0.33 | 0.33 |
| guarded and shifted | 1.33 | 0.53 |
| with its residual | 4.6 | 4.6 |

**The root has no bound free of its guard**, and below the line it is not
merely unproved but wrong. Its `14.5 u²` leans on `divDwDw2_err`, which is the
division's and needs the range. What that range keeps out is a number too
small for the two-product inside the division: below `2^-969` the two-product
misses `s·t ≈ x` by up to three and a half of the smallest numbers there are,
and that miss divided by `2x` is the whole answer. Measured against the exact
root, 20000 numbers a row:

| x | guard passes | worst error |
|---|---|---|
| around 1 | 20000/20000 | 1.99 u² |
| near `2^-969` | 9555/20000 | 991 u² |
| very small | 0/20000 | 2·10²⁴ u² |

**So a number that small is taken up, and the root brought back down.** The
root of a number times four is twice the root of it, and both scalings are by
a power of two, so both are exact. Taken up by `2^1074` — two steps, since
that is more than the whole range — such a number lands at or above one, where
every one of the four tests holds:

| x | guard passes | worst error |
|---|---|---|
| near `2^-969`, scaled | 20000/20000 | 2.06 u² |
| very small, scaled | 20000/20000 | 1.63 u² |

Searched over 300000 numbers: for `x` at or above `2^-969` the guard never
failed at all, and for `x` below it one scaling was always enough. The way
back down is tested rather than argued, as the halving is — scaling up cannot
lose digits, scaling down can — and so is the pair being made of numbers,
which no comparison says, since an infinity is above every line.

**What it is worth, on `sqrt(2^-1060)`:**

| | the bracket | seconds per 100000 |
|---|---|---|
| the residual, as it was | `2^-8.4` wide | 6.1 |
| taken up and brought back | `2^-101` wide | 1.9 |

Eight bits against a hundred and one, and three times quicker. The residual
is still behind both, so the operation stays total, but nothing measured
reaches it any more.

**The module meets the signature.** All 32 obligations are proved and the
check is in the build:

```coq
Module DwFloatCheck <: FloatOps := DwFloat.
```

The square root takes its `q` from `sqrtDw` in `dwarith.v`, one step of
Newton's method on the machine root, which takes it from 16 digits to the 32 a
double word holds. Nothing about `q` is used in the proof, so the step is free
to change.

## Interval will not take it, and why

Sealing was supposed to be the last step: Interval's interval arithmetic is a
functor over a `FloatOps` module, so a sealed module gives intervals over
double words and a *proved* bracket for a whole computation. It does not, and
the reason is worth writing down.

**`div2_correct` cannot be proved for this format.** Interval asks for

```coq
Parameter div2_correct : forall x : type,
  sensible_format = true ->
  1 / 256 <= Rabs (toR x) ->
  toX (div2 x) = (toX x / Xreal 2)%XR.
```

For a single float the condition `1/256 <= |x|` settles it: such a float is
normal, and halving a normal float only decrements its exponent. For a pair the
condition is on the *sum of the two words*. It bounds the high word away from
zero and says nothing about the low one:

```
DWFloat 1 (2^-1074)     sum about 1, so the condition holds easily
                        low word is the smallest subnormal there is
```

Half of that pair is `0.5 + 2^-1075`. Every binary64 number is a whole multiple
of `2^-1074`, so any sum of two of them is one as well, and `2^-1075` is not.
**No pair of floats denotes it**, so no definition of `div2` can meet the
equation. The condition protects one float completely and a pair only partly.

**What the flag actually means.** In both of Interval's own formats it is

```coq
Definition sensible_format :=
  match radix_val radix with Zpos (xO _) => true | _ => false end.
```

— **the radix is even**. That is what it was for: `GenericFloat` and
`SpecificFloat` are parameterised by radix, `div2` and `pow2_UP` cannot work in
an odd radix, so those two obligations are excused there, and the interval
layer then accepts only even radices. All three functors take
`FloatOps with Definition sensible_format := true`
(`Float.v:158`, `Float_full.v:29`, `Transcend.v:30`), which is deliberate: odd
radices are simply not supported above the float layer.

**Our radix is 2.** By the flag's intended meaning we are sensible. We set it
`false` for a quite different reason — subnormals — which is a fair reading of
what `div2_correct` *says*, but not of what the flag was for, and it collides
with that design. The flag conflates two things: the radix being even, and
halving being exact. For a double word the first holds and the second does not,
and the signature gives no way to say so.

So setting it `false` is refused by the functors:

| functor | |
|---|---|
| `FloatInterval` | `Error: field sensible_format ... bodies differ` |
| `FloatIntervalFull` | the same |
| `TranscendentalFloatFast` | the same |

**Refusing a subnormal low word does not do it.** That was the first idea, and
it is wrong, because the obligation is an equation and so the *result* has to be
in the format as well. Take `DWFloat 1 0x1p-1022` — a double word, and its low
word is the smallest normal number there is. Halving both words is exact and
gives `DWFloat 0.5 0x1p-1023`, whose low word is subnormal, so the narrowed
format refuses it and `toX (div2 x)` is `Xnan` where the equation asks for
`Xreal ((1 + 2^-1022) / 2)`. And no other pair denotes that number: a double
word's high word is the rounding of its value, which pins both words. The same
argument kills any floor on the low word, since halving walks straight through
it.

**A floor relative to the high word does do it**, because halving both words
leaves the ratio alone. Ask that the low word be nought or no smaller than
`2^-1000` times the high word. Then `div2` keeps the condition, and under the
obligation's own hypothesis — `1/256 <= |x|`, so the high word is above
`2^-9` — a low word that is not nought is above `2^-1009`, far into the normal
range, so halving it is exact. The cost is a multiplication and two comparisons
on every `real` test, and the arithmetic refuses pairs whose low word is nonzero
and more than `2^-1000` times smaller than the high word — which the arithmetic
does not itself produce, since a low word is either nought or about `2^-53` of
the high one.

**`midpoint_correct` comes with it.** It is the one obligation of the signature
that asks for a result that is *not* `Xnan`, so the midpoint needs a fallback:
take the halved sum when it is real and lies between the two, and the left
endpoint otherwise. That is sound, and bisection loses nothing except in the
cases where the halved sum would have been refused anyway.

## Four definitions changed while sealing

Three of them because the old ones were wrong or unprovable, and they are worth
knowing:

* **`abs` was unsound.** It read the sign of the high word and negated the pair
  or not. On `DWFloat 1 (-inf)` the high word is unsigned, so it returned the
  pair unchanged — and that pair is `Fminfty`, not a valid upper bound. It now
  goes through `onReal`, so a pair that is not a double word gives nothing.
* **`min` and `max` returned the wrong argument on equality.** The signature
  asks for the pair itself in some of its cases, and two pairs can denote the
  same number — or the same infinity — without being the same pair, so
  `min (DWFloat inf 0) (DWFloat inf 1)` was wrong. Both now return the second.
* **`mag`** was the high word's magnitude. That is nearly right but needs the
  half-a-step fact, since a low word of the same sign can push a pair past the
  high word's exponent. It is now the larger of the two words, one step up,
  which needs nothing.
* **`sensible_format`** is `false`, for the reason above.

## The files

Two layers. Below, primitive floats read as real numbers; above, the
algorithms and their bounds.

| file | what it holds |
|---|---|
| `dwbridge.v` | primitive floats as reals: `D2R`, `Dfin`, and each operation |
| `dwarith.v` | the algorithms themselves, on floats, with nothing proved |
| `dwtwosum.v` | `twoSum` and `fastTwoSum`, the error-free sums, on the reals |
| `dwprod.v` | the two-product: its error, and where it has none |
| `dw_updn.v` | the directed operations: the widening steps and the algorithms |
| `dwbound.v` | the bounds themselves, from the steps up to `divDwUp_geP` |
| `dwdivflx.v` | the quotient carried from the paper's format down to the program |
| `dwsqrt.v` | the root: Newton's step, and the error of it |
| `dw_ops.v` | the interface: `DwFloat` and all 32 obligations |
| `test_pi.v` | a smoke test: pi by Machin, and what the operations bracket |
| `Imul.v`, `TwoSumFLT.v` | Knuth's 2Sum in the bounded format, and its grids |
| `F2SumFLT.v` | Fast2Sum in the bounded format |

`dwflx.v` and `dwdivflx.v` read double words in the format with no bottom,
where the ported theorems of `DWPlus.v` and `DWDivDW.v` live: the first carries
the sum down to the program, the second the quotient.

**The quotient and the root are where the interface leans on the ported
development.** `dw_ops.v` takes `div_UP` and `div_DN` from `dwdivflx.v` and
`sqrt_UP` and `sqrt_DN` from `dwsqrt.v`, and so from `DWDivDW.v`,
`DWTimesFP.v`, `DWTimesDW_original.v`, `DWPlus.v`, `Bayleyaux.v`, `F2Sum.v`,
`F2SumFLX.v` and `dwflx.v` behind them — the root needs the sum's bound, which
is `dwflx.v`'s. The sum, the product and the whole numbers are still proved
directly from their residuals and need none of it.

`double-double-arithmetic/` is an untouched archive, kept for inspiration.
Nothing in it is on the build path.

## Three rules the work settled on

**An overflow travels; do not test for it.** An infinity plus anything is an
infinity, so a chain that ran out of range ends in one and the final `real`
test sees it. The one step that broke this was `next_up (-infinity)`, which
gives a number back; `upFp` and `dnFp` in `dw_updn.v` leave alone the infinity
they would undo, and after that no operation needs a guard of its own. The
earlier version, which tested seven intermediates, cost 2.6 times as much
(counted from the source, not timed).

**Every bound asks one thing.** `Dfin (dwlo (op x y))` — that the answer is a
number. The four words given being numbers follows from it, and is read back
out by `addDw_finI`, `mulDw_finI` and their kin.

**Comparing rests on rounding being monotone.** A pair rounds back to its own
high word, so if one pair were at or above another its high word would be too.
That is why comparing high words and then low ones is right, and why
`wellFormed_lt` needs no case analysis on exponents.

**A test is for what propagation cannot settle.** Division keeps one, `posFp`:
the divisor has to be bounded away from zero, and no amount of infinity
travelling establishes that. The root keeps two: the same one, and the sign of
what it is given, since the root of a negative is read as nought here.

**Bound the result for an arbitrary `q`, then apply it.** Division and the root
take a seed from an algorithm nothing is proved about. Stating the bound for
any `q` at all — `divDwUpQ_ge`, `sqrtDwUpQ_ge` — and applying it to the seed
keeps the seed's definition out of the proof. That is not only tidier: with the
seed unfolded, one `have` in the division proof took 574 seconds, and the whole
file now builds in eight.

## Testing

`test_pi.v` computes pi by Machin's formula with the plain operations — right
to about thirty-one digits — and then shows what the interface's own
operations bracket, and what they refuse. It is a smoke test, not a proof: a
proved bracket needs the functors, and the functors need the section above.

`bench_interval.v` proves the same goals twice, once by Interval's tactic as it
ships and once by the same tactic over double words, with `div2_correct`
admitted so that the functors apply. It is not on the build path — native
compilation overflows on it — and is run by hand:

```
coqc -Q . dwarith bench_interval.v
```

Two of its goals take seconds rather than hundredths, and only those say
anything. Measured on this machine, two runs each, seconds:

| goal | bigints | double words |
|---|---|---|
| `method_error`, `i_prec 80` | 5.72 | 1.20 |
| `poly_error`, `i_prec 90` | 0.057 | 0.051 |
| `cancellation`, `i_depth 20`, `i_prec 60` | 74.5 | 22.7 |
| `int_range`, `integral` | 2.83 | 2.88 |
| `int_infinite`, `integral` | 0.347 | 0.358 |
| `exp_table`, `i_prec 61` × 64 | 4.10 | 3.71 |

Three runs, the middle one of each row; the spread was under 4%. About five
times quicker on a Taylor model at eighty bits, about three times on a
bisection run twenty deep at sixty, and level on the other three. **These ask
bigints for the precision each goal needs, which flatters them**; the section
below asks for the width a double word holds, which is the fair question about
the format. The gain is
not a property of the arithmetic on its own — it is where the tactic spends its
time. The full table, and the four goals that are too light to measure, are in
the file.

## The bench, redone

The table above asks bigints for the precision each **goal** needs. That is
the fair question if one is buying a particular proof and the wrong one about
the format, so the measurements below ask bignums for the width a double word
actually holds. The harness is shared with the triple-word development —
`../tttriple/bench/run.sh` and `run_goals.sh` — and generates one file a module
and runs **each in its own process**, twenty thousand operations a loop, the
minimum of five, with an empty loop subtracted. Two mistakes are designed out
of it, both made there first: all the modules in one process inflates whatever
runs last by about 2.7x, and a loop whose accumulator drifts times exponent
alignment as well as the operation.

**One operation at a time**, microseconds:

| op | floats 53 | bignums 53 | bignums 107 | **double words** | |
|---|---|---|---|---|---|
| add | <0.05 | 6.40 | 9.20 | **1.25** | 7.4x |
| sub | <0.05 | 5.55 | 7.50 | **1.00** | 7.5x |
| mul | <0.05 | 7.95 | 16.65 | **1.35** | 12.3x |
| div | <0.05 | 19.35 | 37.25 | **2.15** | 17.3x |
| sqrt | <0.05 | 19.70 | 43.30 | **2.70** | 16.0x |
| cmp | <0.05 | 1.65 | 2.20 | **0.35** | 6.3x |

**Why 107 is the right column, and not 120 or 126.** `BigIntRadix2` keeps a
mantissa as a `zn2z` tree of `int63` words, so capacity goes 63, 126, 252 bits
and the cost **steps** rather than slides — measured, `mul` is 7.5 µs at 53
bits, 9.3 at 63, **17.9 at 64**, 16.6 at 107, 18.9 at 126, **31.6 at 127**,
33.4 at 159. Anything from 64 to 126 bits is the same request, so a double
word's whole range sits in one bignum level.

**That is also why a double word is so much better placed than a triple
word.** A bignum going up a level doubles, 16.6 to 33.4. A word format going
from two floats to three costs **5.6x**, 1.35 to 7.50, because a double-word
product is one two-product and a triple-word product is nine with a
fourteen-term sweep after it. So a double word is 12.3x bignums at its own
width where a triple word is only 4.5x.

**What it delivers, in bits.** `exp x - exp x` at a point has no dependency in
it, so the tightest bound provable reads the precision off directly. A double
word proves `1e-28`, which is bignums at about **97 bits**; on plain arithmetic
— a degree-sixty Horner at a point — it proves `1e-27`, which is bignums at
about **103**. So it loses four bits on arithmetic and ten through `exp`, the
extra six being the series, which runs until a term falls below `2^-prec` and
so takes more terms when the arithmetic is short of its nominal width. Floats
and bignums at 53 bits agree exactly on this test, which is the control.

**Through the tactic**, one process a goal, bignums at 107:

| goal | bignums 107 | **double words** | |
|---|---|---|---|
| pi to 14 digits | 0.028 | **0.014** | 2.0x |
| pi to 24 digits | **0.011** | 0.016 | |
| pi to 34 digits | refused | refused | |
| `method_error` | 6.07 | **1.56** | 3.9x |
| `poly_error` | 0.062 | **0.061** | level |
| `cancellation` | 145.7 | **25.4** | 5.7x |
| `I.exp`, per call | 2.98 ms | **0.42 ms** | 7.1x |

**`cancellation` is not a precision benchmark** and should not be read as one.
What it evaluates at every node is `exp x - exp x` over a range, so its width
is the **dependency**, which every arithmetic returns identically; only
bisection narrows it, at `2^depth`. Primitive floats do it in **0.21
seconds**, a hundred times quicker than a double word, and at the bound and
depth where floats give up so does everything else, up to bignums at two
hundred bits. It measures the cost of one cheap operation a million times over.
`method_error` is the row to read.

## What the division's guard cost, and how it was paid

The `cancellation` row above used to read 24.6 seconds, when `div_UP` and
`div_DN` were bounded by the shift with **no guard and no proof**. Proving them
put a guard on the shift and a residual behind it, and the goal went to 42.9.

| | seconds |
|---|---|
| shift always, unproved | 24.6 |
| guard, and the shift taken | 26.2 |
| guard, and the residual behind it | 42.9 |
| **the same, with the arithmetic mended** | **22.7** |

The first three rows were measured earlier on this machine. The bigint column
of the table above, which nothing here touches, reads 74.5 now where it read
77.6 then, so about four per cent of that fall is the machine and not the
code.

**The guard is cheap and the fallback is not.** Testing cost 7%; taking the
residual cost 68%, because it is ten times a division and it was taken often.

**One condition accounted for all of it.** Dropping the test on `yl * t` alone
brought the goal back to about 26 seconds; dropping the test on `d / yh`
changed nothing. The divisor's low word times the quotient lands in the
subnormal range whenever the divisor is *nearly* a single float — its low word
tiny but not nought.

**And the arithmetic was making such divisors itself.** When a product or a
sum came out exact, the only thing left in the low word was the widening step
— `deps`, or one `next_up` — and that is a subnormal:

```coq
Compute mulDwUp (DWFloat 1 0) (DWFloat 1 0).   (* as it was *)
  = DWFloat 1 5.434722104253712e-323
Compute addDwUp (DWFloat 1 0) (DWFloat 1 0).
  = DWFloat 2 9.8813129168249309e-324
```

The value is exactly 1, and exactly 2. The low word is nothing but noise, and
divide by such a pair and `yl * t` is subnormal at once. Integers, powers of
two and factorials are what a series divides by, so it happened constantly.

**So the sum and the product now answer at once when the answer is exact.**
Both low words nought, and for the product the two-product above `dprodlo` as
well, and the pair is returned unchanged:

```coq
Compute mulDwUp (DWFloat 1 0) (DWFloat 1 0).   (* as it is *)
  = DWFloat 1 0
Compute addDwUp (DWFloat 1 0) (DWFloat 1 0).
  = DWFloat 2 0
```

Then the divisor's low word is nought, `divOk` passes on its own escape, and
the residual is not taken. The division's proof did not change at all.

**The line costs two comparisons, and saves about fifteen operations.**
Measured in Rocq's evaluator, 300000 calls each, seconds:

| | old | new |
|---|---|---|
| `*`, both low words nought | 0.41 | 0.27 |
| `+`, both low words nought | 0.24 | 0.12 |
| `*`, low words not nought | 0.39 | 0.45 |
| `+`, low words not nought | 0.21 | 0.25 |

So about twice as quick where it fires and about 15% slower where it does not.
On the five goals above the slower side does not show, and the quicker side is
worth nineteen seconds.

**The bounds are tighter as well**, which is the same thing said the other way:
an exact product now has an exact answer, where before it carried eleven of the
smallest numbers there are.

## The relaxation that was not taken

The other way out was to drop the `yl * t` test and prove the paper's theorem
stable under the disagreement it hides. Where the test fails the two formats
round `yl * t` differently, but by at most `2^-1074`, which looks like nothing
against a step of `16 u^2` times the answer.

**It is not nothing.** The disagreement does not travel unchanged: two steps
later comes `tl2 = rnd(vl + cl1)`, where `2^-1074` is about one unit in the
last place, so the two runs can part by a whole step. Run in exact arithmetic
on the pairs the test refuses, with the other three conditions holding:

| | worst |
|---|---|
| the program's own error | 3.05 u² |
| the paper's error | 2.82 u² |
| the two answers apart | 3.83 u² |

The operation is right either way — both sit far below the paper's fifteen —
but a *proof* would have to add the gap to the paper's bound, and the room
between the paper's `15 u^2` and the shift's `16 u^2` is one. So the shift
would have to go to `32 u^2`, which is one bit of the hundred and six. That is
a real price, and the line in the sum and the product costs nothing like it.
