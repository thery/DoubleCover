# Bugs found by the proofs

Bugs of elpiDiff found while proving it correct in Rocq. Each was checked on
the Elpi tool, then fixed in Elpi and in its Rocq mirror alike, or refused by
`well_formed` with a diagnostic. After each fix, all the checks passed:
`regress`, `numtest`, `evaltest`, `l2test`, `passtest`, `rocqtest` and,
since the adjoint statement exists, `adjspectest`.

## Tangent mode (2026-10-06, commit 33970b2)

Found while proving `tangent_mode_correct`. Each one is a well-formed program
whose generated tangent was wrong. The conditions were first collected in
`Supported.v` (917021b), then moved into `well_formed` (806650e).

| # | Program | What went wrong | Resolution |
|---|---|---|---|
| 1 | `y = map 1 3 (i\ x * x)`, y of extent 2 | the generated loop wrote `y[1]` and `y[2]`, out of the array, where the map gives `y[0]` and `y[1]` | refused: a map starts at index 0 |
| 2 | y inout, `let s = y[0] in map 0 1 (i\ 1.0)` | the map is constant, not varied, so the tangent did not write `y_dot`, which kept the derivative of the input instead of 0; the adjoint likewise kept the seed as a derivative of the old array | a constant map now writes a zero tangent; a map writing an inout argument is refused (a map writes a dependent argument) |
| 3 | `fold 0 1 y (n w\ fold 0 2 w (j v\ set v j (w[0] + 1)))`, y inout | the source reads `w`, the array before the inner loop, but the generated code read `y`, already updated in place by the inner loop: from `y = [a, b]` the source gives `[a+1, a+1]`, the generated primal `[a+1, a+2]` | refused: an in-place loop nested in another does not read the outer state |
| 4 | `writes y` with body `x`, x an independent array argument | nothing was generated: `y` and `y_dot` were not written | refused: an array computed by the function is built by a map or an in-place loop, not taken from another argument |
| 5 | an independent (or inout) integer `n`, body using `n + 1` | `n + 1` was varied and its tangent read `n_dot`, which is not a parameter (simplify removed the dead definition, but the unsimplified program read an undefined variable) | refused: an independent or inout argument is a real or an array |
| 6 | `writes y`, y a dependent boolean, body `x < 1` | the tangent did not write `y` (the generated L2 is the single definition `const bool t1 = x < 1`; Elpi wrote no header) | refused: a function writes a real or an array |

## Adjoint-value mode (2026-10-09, commit deed0ef)

Found while planning the proof of branches (milestone M2 of the adjoint
proof).

```
primal (function "bri" (arg "u" (array 2) inout u\ arg "c" real independent c\ body (writes u)
  (let (ite (op2 gt c (num "0")) (op2 mul (get u (nat 0)) (get u (nat 0))) (num "0")) z\
   fold (nat 0) (nat 2) u i\ v\
     set v i (op2 add (get v i) z)))).
```

In mode adjoint-value, the forward sweep ran the fold in place on the inout
array `u`. The fold's reverse loop does not need its state, so the old values
of `u` were not recorded. The reverse sweep then replayed the branch, which
read the updated `u[0]` instead of the original value, and the gradient was
wrong: `l2test` gave 10 failures out of 45 checks, all in adjoint-value. Mode
adjoint was right, because it does not run the fold in the forward sweep.

Resolution: an inout argument is passed by value, so adjoint-value does not
give it back anyway (`value_given` excludes it in `AdjointMode.v`). A function
with an inout argument is now annotated as in mode adjoint (`annotate.elpi`;
`Annotate.annotate_cv` in Rocq). In Rocq, `adjoint_body` also gives no value
target for an inout result (`inout_result`); the generated code does not
change. No reference case changed; this one was added as the reference case
`13-branch-inplace`.

## In the test tools (2026-10-07, commit 19f9020)

Not bugs of the generated code: the L2 evaluators had stopped running after
the float builtins were renamed in Elpi (LPCIC/elpi#459).

- `fexp` no longer existed: renamed `exp` (`numbers.elpi`, `evaluate.elpi`).
- `float-op2` clashed with a builtin of the same name: renamed `gallina-op2`
  (`gallina.elpi`; `gallina_op2` in `Gallina.v`).

## Checked, not a bug

- A map writing in place into an inout array, suspected while proving the
  adjoint straight-line case: the tool already refuses it (bug 2 above).
- A dependent array as the state of an in-place fold, suspected to lose the
  value of adjoint-value when the reverse loop restores the state: refused
  ("`u` is declared dependent but the body reads it").
- Booleans that are not passive are counted as carrying a derivative
  (`has_dot`), and the adjoint gives them an adjoint parameter; well-formedness
  rules them out, since only the written argument can be dependent, and it is
  a real or an array (bug 6).
