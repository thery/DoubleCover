# The 16 symmetry fold

Design, pitfalls and measurements for the folded phase 1 table. The source
files say what each definition is; this file says why.

## What it is

The phase 1 heuristic is a distance by rank. The sixteen symmetries fixing
the U/D axis act on ranks, so only one rank per orbit needs storing:
**64 430 orbits against 1 013 760 ranks, 15.73x**. A read folds the rank to
its orbit representative and carries the twist through the same symmetry.

The heuristic is **never asked to be correct**, only to be a local
certificate: everything above `Section P1Heur` in `Phase1.v` consumes two
facts, `p1check0` and `Dp1_step_of_check` (the value drops by at most one
per move). So a folded table need not equal an unfolded one.

## The files

| file | what | needs data |
|---|---|---|
| `Fold.v` | the theory: table and folding functions as section variables, 17 hypotheses | no |
| `FoldTables.v` | the four folding tables unpacked from `P1Fold.v`, and their bounds | yes |
| `FoldStabiliser.v` | `stabC` and `stabE_of_check` | no |
| `FoldRankCert.v` | the pointwise folded step rebuilt into Farp1's rank certificate | no |
| `FoldChecks.v` | the twelve checks as section hypotheses, and what each buys | no |
| `FoldAssembly.v` | the assembly: `FoldChecks` + `FoldRankCert` gives `p1checkStepr` | no |
| `FoldChecksRun.v` | the twelve checks, run | yes |
| `FoldOrbit_NN.v` | the orbit certificate, 27 slices of 81 twists | yes |
| `FoldAtTable.v` | the slots, `stabC`, the glue, `p1check0`, `p1checkStepr` | yes |

The split is deliberate: structure is checked against hypotheses in seconds,
numbers are run last. Before it, one wrong lemma name cost a 40 minute
re-run.

Rebuild order after touching `Phase1.v` or `Fold.v`: Phase1, Fold, FoldTables,
FoldStabiliser, FoldChecks, FoldAssembly, FoldChecksRun, FoldOrbit, FoldAtTable. Anything else gives
"makes inconsistent assumptions over library".

`FoldChecksRun.v`, `FoldOrbit_NN.v` and `FoldAtTable.v` are **out of `_CoqProject`**:
they require `P1Fold`, which does not exist until `mkfold.sh` has run, and
coqdep would refuse the whole project. `mkfold.sh` runs them.

## Measured, 2026-08-10, roquableu

| | |
|---|---|
| the eight table chunks, `ocamlopt -shared` | **9-10 GB each** -- two at a time, seven at once filled 64 GB |
| a certificate slice | ~3 min, 1.4 GB |
| the 27 slices at `-P 9` | 3 waves, **9 min wall, ~1.35 CPU-h** |
| the rank certificate it replaces | ~36 min wall at `-j9`, **~5.4 CPU-h** |
| a search piece | **0.85 GB** against 4.15 for the unfolded table |
| pieces in parallel | 18 (`P1RUN_GB=3`), one wave |
| the folded read, one core | **1.7x slower**; 1.6x faster on four (`bench/lookup`) |

The fold costs the DFS and pays on the table, the certificate and the
memory. Written as one file `foldcheckStep` took over 45 min and had no
observable progress; sliced, it is 9 min and each slice reports its own
time.

## Pitfalls, each one paid for

- **The hazard is not size.** Rows are contiguous, so an out of range index
  reads *another state's valid entry*, not a default. Every `Fold.v`
  hypothesis carries `(r <? nfsi)` or the twist bound for that reason.
- `Fold.v`'s `actrE` is unprovable as stated -- no `fsok x` guard, which
  `Farp1.fsmoveC_inst` needs. Only `Dfoldx_step_of_check` used it, and
  `FoldRankCert.v` makes that unnecessary. Left alone.
- `twsymA` and `msymT` need the twist bound, which makes `tw` implicit; the
  call sites then lose their explicit `tw`.
- **Notations do not capture.** `Notation rankloop body := (... fun r =>
  body)` fails: the argument is read where `r` does not exist. Use real
  combinators -- `allrank`, `alltw`, `allsym`, `allmv`.
- A symmetry loop over `iota 0 16` is unusable: the instance needs
  `f (of_nat s)` unified, not a pattern. Loop over `sym16i : seq int`.
- `exact: hchk` against a loop body **evaluates it**. `rewrite -stabCE;
  exact: hchk` folds the body back to the name instead, and is instant.
- `FoldChecks.v`'s extraction lemmas take their check from its section, so the
  discharged argument order differs from one to the next -- `rrepSn` wants
  `repsi` before the check, being the only one that uses it. Read each
  signature with `About`, never by analogy with a neighbour.
- `by vm_compute` evaluates **twice**, once in the tactic and once when the
  kernel rechecks the cast at `Qed`. Measured on `repslotE`: 1.83 s then
  1.28 s. Use `native_cast_no_check (erefl _)`, or `vm_cast_no_check` where
  no native artifact exists.
- The native step needs `ulimit -s unlimited`; without it `ocamlopt`
  overflows on the table literals.

## Left to do

`Fold.v:250` writes the orbit guard as `(norbi <=? i) || foldstepF tw i`
where `Farp1.v:1335` writes `if ... then true else ...`. The `||` form
evaluates the body on all 2^17 indices instead of the 64 430 admitted --
about 2x. Fixing it invalidates `FoldChecksRun.vo`, so it waits for the next
time that file is rebuilt anyway.
