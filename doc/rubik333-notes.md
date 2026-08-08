# Rubik 3x3x3 — why the code is the way it is

The sources carry one-line comments saying what a definition does.  The
reasons, the traps and the history live here.  Measured numbers live in
`code/Rubik/rubik333_figures.md`.

---

## Strictness: `&&` and `||` are functions

`andb` and `orb` are ordinary functions, so both arguments are evaluated
before the call — under `native_compute` this becomes strict OCaml.  A guard
written `~~ ok x || A` runs `A` on every value; `if ~~ ok x then true else A`
runs it only on the ones the guard lets through.  The same for `&&`.

This has bitten three times, and each time it was worth a large factor:

- `SlrChk` (with `||`) took 719.7 s where `FsmChk` (with `if`) took ~80.
- `fsok x = sok x && ~~ fpar x` evaluated `fpar`, a nat computation, on all
  2^24 values instead of the 12.1 % that pass `sok`.
- `searchz3`'s `issolved x && eq_tabif (rebuild ...)` rebuilt the table at
  every position; `Fast.v` exists to remove that class of waste.

Write nested `if`s in anything the kernel evaluates.

## `Fast.v` — the refinements, and what each one removes

`searchz3f` to `searchz3n` are successive versions of the same search, each
equal to the one before.  `FastP.v` proves `searchz3n = searchz3`.

| | |
|---|---|
| `searchz3f` | the nats leave the inner loop: `allowedr p` precomputed (60.4 us -> 2.55), `nth _ mtis k` becomes an array read (8.67 -> 0.17), `of_nat d` becomes a carried int (1.57 -> 0.10), and `step3i` is six array reads |
| `searchz3g` | the heuristic is tested on the coordinates after the move, so only the positions that survive pay for `comp_tabi` — a 48 entry array that was otherwise built to be thrown away |
| `searchz3h` | `eq_tabif` stops at the first entry that differs, where `eq_tabi`'s `&&` compared all 48 |
| `searchz3k` | `h3le T x di` is `h3i T x <=? di` lookup by lookup: `h3i` took the max of nine lookups where the first usually settles it |
| `searchz3m` | the three conjugates are moved one at a time, so a position rejected on the first never computes the other two |
| `searchz3n` | the move path is carried instead of the composed table; the coordinates say whether a position may be solved, and only then is the table rebuilt.  Sound because a solved cube has solved coordinates, so the test can only let non-solutions through, never reject a solution |

`rebuild` folds with `foldr` over a path kept newest first, which composes the
oldest move first.  An earlier version folded over `rev path` and composed
backwards; nothing detected it, because `rebuild` is only ever evaluated in
the `issolved` branch and no search finds a solution — every answer was "no
solution" either way.  It surfaced only when
`rebuild a0 (k :: path) = comp_tabi 47 (rebuild a0 path) (get mtisa k)` had to
be proved.

## The `fsok` guard

`fsidx x <? nfsi` is **not** the test for "x is a summary", and the three
certificates of `Farp1.v` were false with it.  It fails in both halves of the
packing:

- `srank` returns `nsrank` = 495 both for a twelve bit mask without four bits
  set and as the array default, so `fsidx x = (f + 1) * 495` for those, which
  is below `nfsi = 2048 * 495` for every `f < 2047`.  Counted: 495 of the
  4096 masks are genuine, 3601 are not.
- `fsidx` masks the flip with 2047, not 4095, because bit 11 is the parity of
  the other eleven for a real cube.  But `actf` moves all twelve bits.  At
  `c0 = coordt (id_tab 47)` and `c1 = c0 lxor 2048` the two share a `fsidx`,
  yet after the fourth move their ranks are 300 and 8220.

Together the old guard admitted 8 385 007 of the 2^24 — 50 %, not the 6 % the
comments claimed.  `fsok = sok x && ~~ fpar x` admits exactly
`nflip * nsrank = nfs`.

`fpar` is the parity of the twelve flip bits, and reads only those bits, so
`fpartab` gives it as a 4096 entry lookup and `fparrE` proves the two equal —
`fpar_mask` for the masking, then a certificate over the 4096 masks.  `fsok`
is written as an `if` for the reason at the top of this file.

## Every search optimization belongs in the table check too

The search and the certificates are separate code doing the same kind of
work, so a trick found for one applies to the other.  Applied so far:

- `fpar` as a table and `fsok` as an `if` (see above);
- the loop `all_pow` carrying its offset as an int instead of rebuilding
  `1 << of_nat k` at every node, and nested `if`s in place of `&&`.
  `all_powiE` proves the two loops equal;
- the value that does not depend on the loop variable read once instead of
  eighteen times, in `p1stepF`, `p1stepFr`, `fsmstepF` and `slrstepF`;
- the offset masks `cwmaski` and `fcwmaski` as literals rather than a shift
  and a subtraction on every lookup;
- **the certificate stated over ranks and not over packed values.**
  `p1stepFr` reads `x` only through `fsidx x`, so the loop runs over the
  2^20 ranks rather than the 2^24 packed values — sixteen times fewer, and
  `fsok_lt` carries the result back to any packed value.  The injectivity
  of `fsidx` is *not* needed for this: it is needed for `fsmstepF`, whose
  body really does use `x` (through `actf x`).

Two traps this exposed, worth checking in any evaluated code:

- **`&&` and `||` are function calls**, so both sides run.  In the search
  that wastes the work a short circuit would have skipped; in a certificate
  nothing is skipped, since everything is true, and the gain is only the
  call itself -- still 1.32x at 2^24 nodes a twist.
- **A `let` before a guard runs for every value.**  `let r := fsidx x in if
  ~~ fsok x then ...` computed `fsidx` on all 2^24 rather than on the 6 %
  the guard admits.  Put the `let` in the `else`.

`of_nat` was audited once and `fsidx` fixed; `fpar`'s `count` over an `iota`
and `all_pow`'s own `of_nat` survived that pass, because it looked for the
name `of_nat` rather than for nat computation.  Look for `iota`, `count`,
`odd`, `nth` and `size` as well.

## `fsidx` and `of_nat`

`of_nat` walks its unary argument, so `of_nat 495` is 36.4 us and made
`fsidx` cost 32.0 us against 0.10 us with an int63 literal — 320x.  `fsidx`
is not in the search's inner loop (the search carries ranks) but it is the
guard of every certificate, evaluated 2^24 times in each and 2187 x 2^24
times in `p1checkStep`.  Hence `nsranki`, `nmaski`, `nfsi` and the rest as
literals, each with the nat it stands for in a comment.

## Table bodies must be values, not cons lists

`Definition tab : arr := mkarr n d data.` leaves the body as the *term*
`mkarr n d data`, and `data` is a cons list of tens of thousands of cells.
One delta step then puts that term in front of any tactic that unfolds a
lookup, and the tactic does not return.  `Eval vm_compute in mkarr n d data`
makes the body an array literal and the same tactics run in milliseconds.
A primitive array is not the trigger — the `seq` is.

Corollary for debugging: a proof that is 12 s on one machine and unbounded on
another is a *data* difference, not a tactic difference.  Look at what the
constants in the goal unfold to before touching the tactic.

## The unfolded table

One slot per state, as `ocaml/rubik_par.ml` has it.  The 16 symmetry fold
would shrink the table 15.73x and the certificate with it, but it needs a
soundness lemma of its own (conjugate states land in the same slot) that the
unfolded table does not.  Mimic first, fold later if the size bites.  The
measured cost of not folding is the per worker footprint in the figures file.

## Tactics on the real tables

Restrict the rewrite pattern or give every argument.  Two rewrites that did
not return, both unification searching where it should not:

- `rewrite h3le_split` walks into the two `searchz3` terms — over 240 s,
  against 1.7 s for `rewrite [X in X && _]h3le_split`.
- `searchz3nmE` with `a0`/`path` implicit has to unify `rebuild ?a0 ?path`
  with `a`, which is higher order — over 120 s, against 9 ms with `@` and
  every argument given.

Similarly, a side goal left to `//` or `done` is evaluated: `done` tries
`assumption` and unfolds an `all_pow` at `ncoord = 24`.  Supply the
hypothesis explicitly.

## Building

`ulimit -s unlimited` before any build of `Phase1.v` or below: without it the
*native* pass dies with a stack overflow after every sentence has checked.
`native_cast_no_check` records the cast and the whole evaluation happens in
the kernel at `Qed`, so the `Time` line inside a certificate file always
reads 0 — `time make` is the only measure.
