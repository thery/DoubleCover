# elpiDiff in Rocq

The definitions of elpiDiff in Rocq, mimicking the Elpi code: the same
languages, the same constructors with their arguments in the same order, and
the same evaluators, over the reals of Rocq instead of floats, and all the
passes, one function per Elpi predicate, down to the C++ text, and the proofs
that the passes are correct, with the evaluators as their semantics: the
tangent mode is proved correct (below). The passes compute:
`Compute (main ModeAdjoint "f.elpi" [f])` gives the header Elpi writes.

```
make            # Rocq 9.1; the development is the logical directory ElpiDiff
```

## Theorems

Both modes are proved: [`tangent_mode_correct`](TangentMode.v#L179) (`TangentMode.v`) and
[`adjoint_mode_correct`](AdjointMode.v#L43) (`AdjointMode.v`); the development has no `Admitted`.
`Print Assumptions` of either lists only the axioms
of the reals of the standard library (`sig_forall_dec`, `sig_not_dec`,
`functional_extensionality_dep`, `classic`), which Coquelicot uses as well.

| Theorem | File | Statement |
|---|---|---|
| [`normalize_correct`](Correctness.v#L206) | `Correctness.v` | where the source computes a value, in any domain, its A-normal form computes the same (for a parametric source) |
| [`annotate_correct`](Correctness.v#L292) | `Correctness.v` | the annotated function computes what the function computes |
| [`normalize_parametric`](AnfEquiv.v#L211) | `AnfEquiv.v` | the normal form of a parametric source is parametric: its instances are related |
| [`simplify_correct_tapes`](SimplifyCorrect.v#L2163) | `SimplifyCorrect.v` | simplify preserves the execution over the reals of a program that follows the scoping discipline `good`, tapes included |
| [`duals_derive`](DualsDerive.v#L1491) | `DualsDerive.v` | where f is [`defined`](Smooth.v#L50), it is Fréchet-differentiable as a function of the reals of its arguments (Coquelicot's `filterdiff` on [`Rn`](Euclidean.v#L66)), and the dual numbers compute its derivative |
| [`simulation`](TangentLoops.v#L717) | `TangentLoops.v` | the statements tangent generates for a body compute, over the reals, the value and the tangent of its dual evaluation; the activity analysis is sound |
| [`scoping`](TangentGood.v#L1182) | `TangentGood.v` | those statements follow the discipline `good` |
| [`tangent_simulates_duals_with`](TangentTop.v#L690) | `TangentTop.v` | theorem 1 for a function: the tangent function, run over the reals on the primal arguments, the seeded tangents and any initial values in its output-only tangent parameters ([`tangent_inputs_with`](TangentTop.v#L241)), gives the value and the tangent of the dual evaluation of the normal form of f; [`tangent_simulates_duals`](TangentTop.v#L1151) is its instance with zeros there |
| [`tangent_mode_correct`](TangentMode.v#L179) | `TangentMode.v` | the tangent mode is correct: where a parametric, well-formed f is defined at x, it is differentiable at x with a linear derivative df, and `simplify (tangent (annotate false (normalize f)))`, run over the reals on `tangent_inputs (decls f) x dx`, gives the value of f and df applied to the seed of dx (dx on the independent and inout reals, 0 elsewhere); [`tangent_mode_correct_with`](TangentMode.v#L140) is the same for any initial values of the output-only tangent parameters (`result_dot`, the tangent of a written dependent argument), which are not read |
| [`adjoint_mode_correct`](AdjointMode.v#L43) | `AdjointMode.v` | the adjoint modes are correct: where a parametric, well-formed f is defined at x, it is differentiable at x with a linear derivative df, and the simplified adjoint program, run over the reals on `adjoint_inputs (decls f) x xb yb`, gives a gradient g with <df (seed dx), yb> = <seed dx, g> for every dx (and, in adjoint-value, the value of f) |
| [`adjoint_tangent_agree`](ModesAgree.v#L105) | `ModesAgree.v` | corollary of the two: the two generated programs are adjoint to each other. The tangent program on (x, dx) gives a tangent output w, the adjoint program on (x, xb, yb) a gradient g, and <w, yb> = <seed dx, g> |
| [`tangent_correct`](Main.v#L93), [`adjoint_correct`](Main.v#L110), [`adjoint_value_correct`](Main.v#L127), [`modes_agree`](Main.v#L140) | `Main.v` | the same results in short form, on named pieces: `accepted f x`, `derivative f x df`, `D f x df dx`, [`run_tangent`](Main.v#L48), [`run_adjoint`](Main.v#L62), and the dot product `⟨u, v⟩`; e.g. [`adjoint_correct`](Main.v#L110): the adjoint program gives a gradient g with ⟨D f x df dx, yb⟩ = ⟨seed dx, g⟩ for every dx |

### The adjoint proof

The adjoint program is related to the dual evaluation of the source in an
arbitrary direction dx (the [`pv`](TangentCorrect.v#L147) instance of the tangent proof). The reverse
sweep keeps the *pairing*: the sum, over the storages that carry an adjoint
(the owners), of the tangent of the variable they hold times its adjoint.
Transposing `let x = e` moves the adjoint of x to the operands of e weighted
by the partial derivatives, which keeps the pairing since the tangent of x is
the same combination of the tangents of the operands. A body is simulated by
one lemma for its two sweeps ([`asim_body`](AdjointCorrect.v#L1224)): its forward sweep computes the
values its reverse sweep reads (the to-be-recorded analysis, [`needs`](Tbr.v#L40)), and its
reverse sweep, run from any store that agrees on them, changes the pairing by
the tangent of the body times the seed.

| Milestone | State |
|---|---|
| M1, straight-line bodies (operations, `a[i]`, in-place update) | done: [`asim_straight`](AdjointCorrect.v#L3984) (`AdjointCorrect.v`) and the top level [`adjoint_simulates_duals`](AdjointTop.v#L1002), [`adjoint_straight_duals`](AdjointTop.v#L1765) (`AdjointTop.v`), before [`simplify`](Simplify.v#L292); no `Admitted` |
| M2, branches | done: a branch is replayed in the reverse sweep ([`arev_ite`](AdjointBranch.v#L1426), `AdjointBranch.v`), and the top level [`adjoint_branchy_duals`](AdjointTop.v#L1796) (`AdjointTop.v`, now a corollary of [`adjoint_nesty_duals`](AdjointTop.v#L1736) through the inclusions [`straight_branchy`](AdjointFoldy.v#L258), [`branchy_foldy`](AdjointFoldy.v#L288), [`foldy_nesty`](AdjointTop.v#L1730)), for bodies of straight lets and branches with no assignment in a branch; no `Admitted`. The proof found that adjoint-value lost the original value of an inout array (see `BUGS.md`, fixed in deed0ef) |
| M3, maps | done: [`afwd_map`](AdjointBranch.v#L1636), [`arev_map`](AdjointBranch.v#L1817) (`AdjointBranch.v`): the reverse loop replays the body at each index and transposes it from the adjoint of the element, the written array, dependent, having a zero tangent; [`adjoint_branchy_duals`](AdjointTop.v#L1796) now covers maps at the end of the function; no `Admitted` |
| M4, scalar folds and tapes | done: [`afwd_fold`](AdjointBranch.v#L2148), [`arev_fold`](AdjointBranch.v#L2455) (`AdjointBranch.v`): the forward sweep pushes the state on a tape before each step when the reverse loop reads it ([`fold_tape`](AdjointCorrect.v#L962)); the reverse loop pops it, replays the body and transposes it with the state as an extra owner, and the initial value receives the adjoint of the first state; [`adjoint_branchy_duals`](AdjointTop.v#L1796) now covers scalar folds at the top level; no `Admitted` |
| M5, in-place array folds | done: [`afwd_fold_nbody`](AdjointNBody.v#L1268), [`arev_fold_nbody`](AdjointNBody.v#L1283) (`AdjointNBody.v`, with the pieces of `AdjointFold.v`): the forward sweep pushes on the tape of the array the element each step overwrites, when the reverse loop reads it; the reverse loop pops it back before replaying the step; [`adjoint_foldy_duals`](AdjointTop.v#L1826) (`AdjointTop.v`) covers them at the top level, [`foldy`](AdjointFoldy.v#L237) being a subclass of [`nesty`](AdjointNesty.v#L25). Nests of any depth (`AdjointNBody.v`): an in-place fold whose steps end with a set, with an in-place fold of their state whose steps are again such bodies, or with the state itself ([`nbody`](AdjointNBody.v#L21)); a state whose step ends with a fold or gives it back is never read by the reverse sweep ([`nbody_state_dead`](AdjointNBody.v#L364), [`nbody_ret_dead`](AdjointNBody.v#L444)), and each step's reverse sweep restores the state and pops what its inner fold pushed ([`tail_back`](AdjointCorrect.v#L1056), [`arev_fold_nbody`](AdjointNBody.v#L1283)); [`adjoint_nesty_duals`](AdjointTop.v#L1736) covers them; no `Admitted`, only the axioms of the reals |
| M6, [`simplify`](Simplify.v#L292) with tapes, the scoping of the adjoint code | done: [`simplify_correct_tapes`](SimplifyCorrect.v#L2163) (`SimplifyCorrect.v`), simplify is correct on programs with tapes (a push or a pop writes its tape, in `simplify.elpi` as well); the scoping discipline of the adjoint code (`AdjointGood.v`: scope indexed by what the code reads, tapes declared before push and pop, bars declared before increment), for every body and value with no body class: [`agood_fwd`](AdjointGoodFwd.v#L1092) (`AdjointGoodFwd.v`) and [`agood_adj`](AdjointGoodRev.v#L1663) (`AdjointGoodRev.v`); at the top, [`adjoint_good`](AdjointGoodTop.v#L122) and [`adjoint_nesty_simplified`](AdjointGoodTop.v#L414) (`AdjointGoodTop.v`): the simplified adjoint function computes the gradient |
| M7, adjoint-value at the top, [`adjoint_mode_correct`](AdjointMode.v#L43) | done: every well-formed program is in the class [`nesty`](AdjointNesty.v#L25) ([`well_formed_nesty`](AdjointClassify.v#L631), `AdjointClassify.v`, by parametricity from the typechecked instance; [`nesty`](AdjointNesty.v#L25) quantifies its lets only over binders of their type), so [`adjoint_wf_duals`](AdjointWf.v#L22) (`AdjointWf.v`) has no class premise; [`adjoint_mode_correct_from`](AdjointModeProof.v#L74) (`AdjointModeProof.v`) derives the final statement (differentiability by [`duals_derive`](DualsDerive.v#L1491), the gradient as the transpose of df through the pairing identity in every direction), and [`adjoint_mode_correct`](AdjointMode.v#L43) (`AdjointMode.v`) is proved from it, [`adjoint_nesty_simplified`](AdjointGoodTop.v#L414) and [`well_formed_nesty`](AdjointClassify.v#L631). `AdjointExamples.v` checks the class premise on 21 programs the tool accepts |

Proved in `AdjointCorrect.v`: the operations are linear in the tangents with
the spelled partial derivatives as coefficients; the forward sweep of each
operation computes its value (pushing the overwritten element on the tape of a
recorded storage); the reverse sweep of each operation transposes it, reading
only scalars that occur in it; typing and activity of the values (a value not
varied has a zero tangent); the let, with a fresh variable or updated in
place; returns, with the value adjoint-value leaves; the reverse sweep keeps the
value adjoint-value leaves ([`vo_kept`](AdjointCorrect.v#L641): the reverse code of a straight value
writes only adjoints); [`asim_straight`](AdjointCorrect.v#L3984).

Proved in `AdjointTop.v` ([`adjoint_simulates_duals`](AdjointTop.v#L1002), Qed, for any body
simulated by [`asim_body`](AdjointCorrect.v#L1224)): the arguments of the adjoint function laid out in
the store, the forward context, the prologue and the seed of each result (a
returned real; a written real, dependent or inout; a written array), the
reverse sweep from the owners (the arguments with an adjoint), the final
adjoints read back as the gradient, `<tangent v, yb> = <seed dx, g>`, and the
value in adjoint-value. Its hypothesis `length dx = in_dim x` was added, and
the Boolean arguments that carry an adjoint are excluded by well-formedness.

## Files

| Rocq | Elpi | Contents |
|---|---|---|
| `Dot.v` | — | [`dotl`](Dot.v#L11), the dot product of two lists of reals, shared by the adjoint statements and proofs |
| `Syntax.v` | `syntax.elpi` (and the operators of `operations.elpi`) | L0: [`unary`](Syntax.v#L20), [`binary`](Syntax.v#L25), [`term`](Syntax.v#L34), [`ty`](Syntax.v#L61), [`role`](Syntax.v#L69), [`result`](Syntax.v#L78), [`definition`](Syntax.v#L88), [`function`](Syntax.v#L95), [`decl`](Syntax.v#L101); [`written_role`](Syntax.v#L105), [`varied_role`](Syntax.v#L109) |
| `Anf.v` | the types of `anf.elpi` | L1 and L1ᵃ: [`atom`](Anf.v#L17), `value`, `anf`, [`aresult`](Anf.v#L38), [`adefinition`](Anf.v#L42), [`afunction`](Anf.v#L79), [`pexpr`](Anf.v#L49); the annotations [`bare`](Anf.v#L68) and [`ann`](Anf.v#L70) |
| `Derivative.v` | the types of `derivative.elpi` | L2: [`dvar`](Derivative.v#L17), [`dexpr`](Derivative.v#L27), [`dsort`](Derivative.v#L36), [`dstmt`](Derivative.v#L42), [`dpass`](Derivative.v#L62), [`dparam`](Derivative.v#L69), [`dreturn`](Derivative.v#L72), [`dbody`](Derivative.v#L76), [`scoped`](Derivative.v#L81), [`dfunction`](Derivative.v#L108) |
| `Target.v` | `target.elpi` | L3: [`expr`](Target.v#L8), [`stmt`](Target.v#L15), [`cfunction`](Target.v#L32) |
| `Domain.v` | `numbers.elpi` | [`domain`](Domain.v#L23); the reals ([`reals`](Domain.v#L144)), for Elpi's floats; dual numbers over any domain ([`duals`](Domain.v#L213)) |
| `Eval.v` | `eval.elpi` | [`val`](Eval.v#L19); the evaluator of L0 ([`eval`](Eval.v#L110), [`eval_function`](Eval.v#L159)) |
| `Smooth.v` | — | the partial semantics of Abadi and Plotkin: the domain [`smooth_reals`](Smooth.v#L43), the predicate [`defined`](Smooth.v#L50) |
| `EvalAnf.v` | `eval-anf.elpi` | the evaluator of L1 and L1ᵃ ([`aeval`](EvalAnf.v#L28), [`aeval_function`](EvalAnf.v#L77)) |
| `Exec.v` | `exec.elpi` | the evaluator of L2 ([`exec`](Exec.v#L117), [`exec_dfunction`](Exec.v#L194)) |
| `Operations.v` | the table of `operations.elpi` | [`operation1`](Operations.v#L28), [`operation2`](Operations.v#L65) (the rows, first row or first match), [`extra_arguments`](Operations.v#L42), [`partial1`](Operations.v#L86), [`partial2`](Operations.v#L104), [`unary_name`](Operations.v#L121), [`binary_name`](Operations.v#L130) |
| `Normalize.v` | the pass of `anf.elpi` | [`normalize`](Normalize.v#L87) (L0 to L1: [`norm`](Normalize.v#L21), [`norm_body`](Normalize.v#L47), [`normalize_definition`](Normalize.v#L61)), [`expressible`](Normalize.v#L83), [`declarations`](Normalize.v#L92) |
| `WellFormed.v` | `well-formed.elpi` | [`diagnostic`](WellFormed.v#L20); [`well_formed`](WellFormed.v#L403), [`typecheck`](WellFormed.v#L143), `typecheck_value`, `type_of`, `occurs`, [`reads_around_inner_loop`](WellFormed.v#L128) |
| `Atoms.v` | the atom sets and `atoms-of` of `anf.elpi` | [`avar`](Atoms.v#L17) (the variables of the analyses), [`same_term`](Atoms.v#L24), [`atom_member`](Atoms.v#L32), [`atom_remove`](Atoms.v#L35), [`atom_union`](Atoms.v#L40), `atoms_of_*` |
| `Activity.v` | `activity.elpi` | [`varied`](Activity.v#L16), [`varied_value`](Activity.v#L21), `varied_anf`, [`fold_varied`](Activity.v#L41), [`let_binder`](Activity.v#L47), [`fold_binders`](Activity.v#L50) |
| `Tbr.v` | `tbr.elpi` | [`sweep`](Tbr.v#L19); [`needs`](Tbr.v#L40), `value_needs`, [`read_by`](Tbr.v#L30), `records`, `records_in`, [`state_live`](Tbr.v#L120) |
| `Annotate.v` | `annotate.elpi` | [`annotate`](Annotate.v#L134) (L1 to L1ᵃ), in two traversals |
| `Transform.v` | the helpers of `derivative.elpi` | `tvar` (the variables of the transformations), [`sbind`](Transform.v#L46), [`sflatten`](Transform.v#L55), [`spell`](Transform.v#L63), [`dot`](Transform.v#L88), [`bar`](Transform.v#L95), [`scale`](Transform.v#L101), [`sum`](Transform.v#L109), [`with_storage`](Transform.v#L138), the opening of binders, [`with_arguments`](Transform.v#L190), `type_of` |
| `Tangent.v` | `tangent.elpi` | `tangent` (L1ᵃ to L2): [`tan`](Tangent.v#L100), `tan_value`, [`tangent_result`](Tangent.v#L45), … |
| `Dump.v` | the printer of L2 in `dump.elpi` | [`pr_dfunction`](Dump.v#L105): the lines of `dump -- derivative <mode>` |
| `Adjoint.v` | `adjoint.elpi` | [`adjoint`](Adjoint.v#L315) (L1ᵃ to L2), modes [`adjoint`](Adjoint.v#L315) and `adjoint-value`: [`prim`](Adjoint.v#L141) and `fwd_value`, then [`adj`](Adjoint.v#L203) and `rev_value` |
| `Simplify.v` | `simplify.elpi` | [`simplify`](Simplify.v#L292) (L2 to L2′): [`simplify_expr`](Simplify.v#L60), [`simplify_stmts`](Simplify.v#L158), `fuse`, with a fuel |
| `Lower.v` | `lower.elpi` | [`lower`](Lower.v#L90) (L2′ to L3), the counter of the names threaded; [`lower_all`](Lower.v#L100), the functions of a file |
| `Cxx.v` | `cxx.elpi` | [`function_string`](Cxx.v#L99), [`header_string`](Cxx.v#L111): the C++ text |
| `Gallina.v` | `gallina.elpi` | [`gallina_file`](Gallina.v#L379): the derivative programs after simplification as Gallina, for CertiRocq (assignments threaded as lets, loops `for_up`/`for_down`, reals primitive floats) |
| `Adjudge.v` | the driver of `adjudge.elpi` | [`mode`](Adjudge.v#L16), [`check`](Adjudge.v#L26), [`differentiate`](Adjudge.v#L31), [`transform`](Adjudge.v#L39), [`main`](Adjudge.v#L44): the header and the diagnostics of a case |
| `Scoping.v` | — | [`open_pairs`](Scoping.v#L27), the opening of a generated function with the numbers simplify and the evaluator use; `good`, the scoping discipline of L2 |
| `SimplifyCorrect.v` | — | theorem 2: [`simplify_correct_tapes`](SimplifyCorrect.v#L2163) |
| `Correctness.v` | — | [`parametric`](Correctness.v#L73) (PHOAS relations of L0); [`normalize_correct`](Correctness.v#L206), [`annotate_correct`](Correctness.v#L292) |
| `AnfEquiv.v` | — | [`anf_eq`](AnfEquiv.v#L33), the relation of two instances of L1; [`normalize_parametric`](AnfEquiv.v#L211) |
| `Euclidean.v` | — | [`Rn`](Euclidean.v#L66), R^n as a normed module of Coquelicot; vectors and lists |
| `DualsDerive.v` | — | theorem 3: the domain of the functions of a point with their derivative; [`value_of`](DualsDerive.v#L1305), [`dual_args`](DualsDerive.v#L1315); [`duals_derive`](DualsDerive.v#L1491) |
| `TangentCorrect.v` | — | theorem 1, the simulation: [`pv`](TangentCorrect.v#L147), the record of the four instances; the invariants ([`static_ok`](TangentCorrect.v#L165), [`store_ok`](TangentCorrect.v#L178), [`ctx_ok`](TangentCorrect.v#L231)); the cases of returns, lets, operations, branches |
| `TangentLoops.v` | — | the loops of the simulation (map, scalar fold, in-place fold); [`simulation`](TangentLoops.v#L717) |
| `TangentGood.v` | — | the scoping discipline of the tangent code: [`scoping`](TangentGood.v#L1182) |
| `TangentTop.v` | — | the layout of the tangent function (`seed`, `tangent_inputs`, [`tangent_inputs_with`](TangentTop.v#L241), `tangent_output`); [`tangent_simulates_duals_with`](TangentTop.v#L690), [`tangent_simulates_duals`](TangentTop.v#L1151) |
| `TangentMode.v` | — | [`tangent_mode_correct_with`](TangentMode.v#L140), [`tangent_mode_correct`](TangentMode.v#L179) |
| `AdjointSpec.v` | — | the layout of the adjoint function: [`adjoint_inputs`](AdjointSpec.v#L50) (primal arguments, initial adjoints xb or the seed yb, the seed of a returned value), [`adjoint_output`](AdjointSpec.v#L105) (the gradient: final minus initial adjoints), [`value_given`](AdjointSpec.v#L87) |
| `AdjointNBody.v` | — | in-place loops of any depth: the class [`nbody`](AdjointNBody.v#L21) (ops and reads ending with a set, an inner in-place fold on the state, or the state), [`afwd_fold_nbody`](AdjointNBody.v#L1268), [`arev_fold_nbody`](AdjointNBody.v#L1283), [`nbody_asim`](AdjointNBody.v#L2038) |
| `AdjointClassify.v` | — | the classification: [`well_formed_nesty`](AdjointClassify.v#L631), every well-formed function has its opened body in [`nesty`](AdjointNesty.v#L25), through a second pv instance opened at fresh binders ([`fpv`](AdjointClassify.v#L29)) and related to the target by [`hinv`](AdjointClassify.v#L34) |
| `AdjointGood.v`, `AdjointGoodFwd.v`, `AdjointGoodRev.v` | — | the scoping discipline of the adjoint code and its proof for every body: [`agood_fwd`](AdjointGoodFwd.v#L1092), [`agood_adj`](AdjointGoodRev.v#L1663) |
| `AdjointWf.v` | — | [`adjoint_wf_duals`](AdjointWf.v#L22): the adjoint simulation for every parametric, well-formed function |
| `AdjointMode.v` | — | theorem [`adjoint_mode_correct`](AdjointMode.v#L43): where f is defined, for every tangent dx, <df (seed dx), yb> = <seed dx, g>, and adjoint-value gives the value of f back (unless f writes an inout argument) |
| `ModesAgree.v` | — | `tangent_code`, [`adjoint_code`](ModesAgree.v#L95); [`filterdiff_locally_unique`](ModesAgree.v#L73) (a Fréchet derivative is unique); corollary [`adjoint_tangent_agree`](ModesAgree.v#L105) |
| `Main.v` | — | the final theorems in short form: [`derivative_exists`](Main.v#L83), [`tangent_correct`](Main.v#L93), [`adjoint_correct`](Main.v#L110), [`adjoint_value_correct`](Main.v#L127), [`modes_agree`](Main.v#L140) |
| `AdjointExamples.v` | — | non-vacuity: the accepted reference cases proved to be in the class of [`adjoint_nesty_duals`](AdjointTop.v#L1736) |
| `AdjointModeProof.v` | — | [`adjoint_mode_correct_from`](AdjointModeProof.v#L74): [`adjoint_mode_correct`](AdjointMode.v#L43) from the simplified adjoint corollary |

## From Elpi to Rocq

- **Binders.** Elpi's λ-tree syntax (`let E (x\ B)`) becomes PHOAS, parametric
  higher-order abstract syntax: a type of terms is parameterized by the type V
  of its variables, a binder is a Rocq function, `Let_ (e : term V) (b : V ->
  term V)`, and a variable is `Var x`. A closed program is quantified over V:
  `fdef : forall V, definition V`. As in Elpi, no term names a variable with a
  string.
- **Evaluators.** An Elpi evaluator opens a binder with a hypothesis
  (`value-of x V`); a Rocq evaluator instantiates V with the values and applies
  the binder, `eval (b v)`. The evaluator of L2 instantiates V with numbers,
  allocated in order, as Elpi opens the binders with fresh variables (`pi`), so
  that the store can compare them.
- **Relations become functions into `option`.** `None` where the Elpi predicate
  fails: an ill-typed program, an index out of an array, an unknown operator.
- **Comparisons return an option.** A comparison is decided by an `if` in
  Elpi, which never fails. In Rocq it returns an `option bool`, so that a
  domain may refuse a tie: the partial semantics of Abadi and Plotkin (POPL
  2020), where a comparison of two equal reals is undefined ([`smooth_reals`](Smooth.v#L43),
  in `Smooth.v`). [`reals`](Domain.v#L144) and [`duals`](Domain.v#L213) never refuse: the evaluators of Elpi are
  mimicked as before.
- **Numbers.** Elpi's floats become the reals of Rocq (`R`); a literal, a
  string as in Elpi (`"0.9"`, `"13.0 / 12.0"`), is read exactly, as a rational
  number. Elpi's `int` becomes `Z`.
- **Names.** The constructors keep their Elpi names, capitalized (`num` →
  `Num`, `op1` → `Op1`); the prefixes `a-` and `d-` become `A` and [`D`](Main.v#L43)
  (`a-let` → `ALet`, `d-for-back` → `DForBack`); the three reserved words of
  Rocq take an underscore (`set` → `Set_`, `let` → `Let_`, [`function`](Syntax.v#L95) →
  `Function_`). A predicate keeps its name with `_` for `-` (`eval-function` →
  [`eval_function`](Eval.v#L159)).
- **Passes.** An Elpi pass that opens a binder with a hypothesis relating it
  to its image (`as-atom x a` in [`normalize`](Normalize.v#L87)) instantiates, in PHOAS, the
  variables of its input with the terms of its output: [`normalize`](Normalize.v#L87) takes a
  `term (atom V)`, so a source variable is its atom. A continuation-passing
  predicate (`norm T K R`) becomes a function taking its continuation.
- **Hypotheses on variables.** Where Elpi opens a binder with hypotheses on
  its variable (`of x T`, `argument x N R` in `well-formed`), the variables are
  instantiated with the record of that information ([`vinfo`](WellFormed.v#L25)), whose identity,
  numbered in order, is what Elpi's [`same_term`](Atoms.v#L24) and `occurs` compare.
- **A pass whose input and output need different variables.** [`annotate`](Annotate.v#L134)
  reads its input with the variables of the analyses ([`avar`](Atoms.v#L17): an identity and
  whether it is varied) and builds a term over any variables V. Elpi does both
  in one traversal; in PHOAS the closed input is instantiated twice: a first
  traversal computes the annotations into a tree that follows the lets and
  folds, a second rebuilds the term with them.
- **The transformations.** The variables of L1ᵃ are instantiated with what
  Elpi's hypotheses say of them (`tvar`: the variable of the generated code
  that holds it, its type, whether it is varied, its argument), whose stored
  variable is a variable of the output: a transformation is one traversal.
  `recorded N`, on a storage, becomes a flag inherited by the variables stored
  in the storage of another; `written Y`, compared with an atom, an identity
  of the arguments.
- **A counter global to the run.** Elpi's `new-name` draws the numbers of the
  locals from `new_int`, global to the run, so they are numbered across the
  functions of a file: [`lower`](Lower.v#L90) threads the counter.
- **Relations queried in several modes.** [`operation2`](Operations.v#L65) has several rows per
  operator and a cut on the first: the table is kept as rows, with one
  function per use ([`operation2`](Operations.v#L65), the first row; [`operation2_typed`](Operations.v#L70), the
  first row matching given operand types).
- **One declaration per type.** [`comparison`](Operations.v#L78), defined in `activity.elpi` from
  the operations table, is in `Operations.v`, with the same definition, so that
  the evaluators use it too. A Rocq inductive is declared in one place:
  the operators of `operations.elpi` are in [`unary`](Syntax.v#L20) and [`binary`](Syntax.v#L25) with
  `unknown1` and `unknown2` of `syntax.elpi`; `v-tape` of `exec.elpi` is in
  [`val`](Eval.v#L19) with the values of `eval.elpi`; the key `returned` of `exec.elpi` is a
  constructor of the keys of the store, next to the variables.


## Checking against Elpi

`~/claudeExp/elpi/tools/rocqtest.py` (outside the repository, with the reference
cases) prints the functions of every case as Rocq terms (`torocq.elpi`), and
compares what Rocq computes with what Elpi prints: the diagnostics, and the
derivative programs printed by [`pr_dfunction`](Dump.v#L105) against `dump -- derivative|simplified
<mode>`, and the complete C++ headers against those [`main`](Adjudge.v#L44) writes, for the three
modes: 141 comparisons on the reference cases, all identical, line for line and
character for character.
