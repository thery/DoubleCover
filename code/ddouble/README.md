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
| `div_UP` / `div_DN` | `divDwUp` / `divDwDn` | proved |
| `sqrt_UP` / `sqrt_DN` | `sqrtDwUp` / `sqrtDwDn` | proved |

Everything proved is admit-free; the assumptions are the primitive-float and
primitive-integer axioms and the classical reals, nothing else.

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

**The escape the signature offers does not work.** `sensible_format` is the
module's own field, so setting it to `false` makes `div2_correct` — and
`midpoint_correct` — vacuous, and that is what this module does. But all three
of Interval's functors take not `FloatOps` but `FloatOps` with
`sensible_format` fixed to `true`:

| functor | |
|---|---|
| `FloatInterval` | `Error: field sensible_format ... bodies differ` |
| `FloatIntervalFull` | the same |
| `TranscendentalFloatFast` | the same |

So the excuse is written into the signature and then made unusable by the
functors. Both of Interval's own formats set the field to `true`, so nobody
appears to have reached this before.

**The way through**, when someone takes it, is to narrow the format: a pair
stops counting as a double word when its low word is subnormal. Then `xl / 2`
is exact, `div2_correct` is provable, `sensible_format` can be `true`, and the
functors apply. It costs two float comparisons on every `real` test, and the
arithmetic then refuses pairs whose low word is below about `2^-1022` — the
region below `2^-969` in value, where the two-product already gives up.

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
| `dwprod.v` | the two-product, handed to Flocq's own Dekker theorem |
| `dw_updn.v` | the directed operations: the widening steps and the algorithms |
| `dwbound.v` | the bounds themselves, from the steps up to `divDwUp_geP` |
| `dw_ops.v` | the interface: `DwFloat` and all 32 obligations |
| `test_pi.v` | a smoke test: pi by Machin, and what the operations bracket |
| `Imul.v`, `TwoSumFLT.v` | Knuth's 2Sum in the bounded format, and its grids |
| `F2SumFLT.v` | Fast2Sum in the bounded format |

`dwflx.v` reads double words in the format with no bottom, where the ported
theorems of `DWPlus.v` live. **Nothing depends on it today**: the bounds are
all proved directly, so it — and with it `F2SumFLX.v`, `F2Sum.v`,
`Bayleyaux.v` and `DWPlus.v` — is a spur kept for the error analyses that a
tighter algorithm would need.

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
