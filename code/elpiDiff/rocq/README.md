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

Both modes are proved: [`tangent_mode_correct`](proofs/tangent/TangentMode.v#L179) (`TangentMode.v`) and
[`adjoint_mode_correct`](proofs/adjoint/AdjointMode.v#L43) (`AdjointMode.v`); the development has no `Admitted`.
`Print Assumptions` of either lists only the axioms
of the reals of the standard library (`sig_forall_dec`, `sig_not_dec`,
`functional_extensionality_dep`, `classic`), which Coquelicot uses as well.

| Theorem | File | Statement |
|---|---|---|
| [`normalize_correct`](proofs/passes/Correctness.v#L206) | `Correctness.v` | where the source computes a value, in any domain, its A-normal form computes the same (for a parametric source) |
| [`annotate_correct`](proofs/passes/Correctness.v#L292) | `Correctness.v` | the annotated function computes what the function computes |
| [`normalize_parametric`](proofs/passes/AnfEquiv.v#L211) | `AnfEquiv.v` | the normal form of a parametric source is parametric: its instances are related |
| [`simplify_correct_tapes`](proofs/passes/SimplifyCorrect.v#L2163) | `SimplifyCorrect.v` | simplify preserves the execution over the reals of a program that follows the scoping discipline `good`, tapes included |
| [`duals_derive`](math/DualsDerive.v#L1491) | `DualsDerive.v` | where f is [`defined`](eval/Smooth.v#L50), it is Fréchet-differentiable as a function of the reals of its arguments (Coquelicot's `filterdiff` on [`Rn`](math/Euclidean.v#L66)), and the dual numbers compute its derivative |
| [`simulation`](proofs/tangent/TangentLoops.v#L717) | `TangentLoops.v` | the statements tangent generates for a body compute, over the reals, the value and the tangent of its dual evaluation; the activity analysis is sound |
| [`scoping`](proofs/tangent/TangentGood.v#L1182) | `TangentGood.v` | those statements follow the discipline `good` |
| [`tangent_simulates_duals_with`](proofs/tangent/TangentTop.v#L690) | `TangentTop.v` | theorem 1 for a function: the tangent function, run over the reals on the primal arguments, the seeded tangents and any initial values in its output-only tangent parameters ([`tangent_inputs_with`](proofs/tangent/TangentTop.v#L241)), gives the value and the tangent of the dual evaluation of the normal form of f; [`tangent_simulates_duals`](proofs/tangent/TangentTop.v#L1151) is its instance with zeros there |
| [`tangent_mode_correct`](proofs/tangent/TangentMode.v#L179) | `TangentMode.v` | the tangent mode is correct: where a parametric, well-formed f is defined at x, it is differentiable at x with a linear derivative df, and `simplify (tangent (annotate false (normalize f)))`, run over the reals on `tangent_inputs (decls f) x dx`, gives the value of f and df applied to the seed of dx (dx on the independent and inout reals, 0 elsewhere); [`tangent_mode_correct_with`](proofs/tangent/TangentMode.v#L140) is the same for any initial values of the output-only tangent parameters (`result_dot`, the tangent of a written dependent argument), which are not read |
| [`adjoint_mode_correct`](proofs/adjoint/AdjointMode.v#L43) | `AdjointMode.v` | the adjoint modes are correct: where a parametric, well-formed f is defined at x, it is differentiable at x with a linear derivative df, and the simplified adjoint program, run over the reals on `adjoint_inputs (decls f) x xb yb`, gives a gradient g with <df (seed dx), yb> = <seed dx, g> for every dx (and, in adjoint-value, the value of f) |
| [`adjoint_tangent_agree`](proofs/adjoint/ModesAgree.v#L105) | `ModesAgree.v` | corollary of the two: the two generated programs are adjoint to each other. The tangent program on (x, dx) gives a tangent output w, the adjoint program on (x, xb, yb) a gradient g, and <w, yb> = <seed dx, g> |
| [`tangent_correct`](top/Main.v#L93), [`adjoint_correct`](top/Main.v#L110), [`adjoint_value_correct`](top/Main.v#L127), [`modes_agree`](top/Main.v#L140) | `Main.v` | the same results in short form, on named pieces: `accepted f x`, `derivative f x df`, `D f x df dx`, [`run_tangent`](top/Main.v#L48), [`run_adjoint`](top/Main.v#L62), and the dot product `⟨u, v⟩`; e.g. [`adjoint_correct`](top/Main.v#L110): the adjoint program gives a gradient g with ⟨D f x df dx, yb⟩ = ⟨seed dx, g⟩ for every dx |
| [`adjoint_componentwise`](top/Main.v#L282) | `Main.v` | the gradient component by component: for every input real i that f is differentiated with respect to (`diff_wrt f x i`), the i-th component of g is ⟨D f x df (e x i), yb⟩, with `e x i` the i-th standard basis vector; equivalent to the dot-product form by [`dotl_ext`](math/Dot.v#L34) (`Dot.v`) |
| [`adjoint_jacobian`](top/MainMx.v#L45) | `MainMx.v` | the same with the Jacobian matrix J (mathcomp): for an input i f is differentiated with respect to, the i-th component of the gradient is the sum over j of yb_j times J j i, i.e. g = Jᵀ yb. This matrix layer uses one more axiom, `constructive_indefinite_description` (R as a mathcomp ring, `RMat.v`); the other theorems do not |

### The adjoint proof

The adjoint program is related to the dual evaluation of the source in an
arbitrary direction dx (the [`pv`](proofs/tangent/TangentCorrect.v#L147) instance of the tangent proof). The reverse
sweep keeps the *pairing*: the sum, over the storages that carry an adjoint
(the owners), of the tangent of the variable they hold times its adjoint.
Transposing `let x = e` moves the adjoint of x to the operands of e weighted
by the partial derivatives, which keeps the pairing since the tangent of x is
the same combination of the tangents of the operands. A body is simulated by
one lemma for its two sweeps ([`asim_body`](proofs/adjoint/AdjointCorrect.v#L1224)): its forward sweep computes the
values its reverse sweep reads (the to-be-recorded analysis, [`needs`](analysis/Tbr.v#L40)), and its
reverse sweep, run from any store that agrees on them, changes the pairing by
the tangent of the body times the seed.

| Milestone | State |
|---|---|
| M1, straight-line bodies (operations, `a[i]`, in-place update) | done: [`asim_straight`](proofs/adjoint/AdjointCorrect.v#L3984) (`AdjointCorrect.v`) and the top level [`adjoint_simulates_duals`](proofs/adjoint/AdjointTop.v#L1002), [`adjoint_straight_duals`](proofs/adjoint/AdjointTop.v#L1765) (`AdjointTop.v`), before [`simplify`](modes/Simplify.v#L292); no `Admitted` |
| M2, branches | done: a branch is replayed in the reverse sweep ([`arev_ite`](proofs/adjoint/AdjointBranch.v#L1426), `AdjointBranch.v`), and the top level [`adjoint_branchy_duals`](proofs/adjoint/AdjointTop.v#L1796) (`AdjointTop.v`, now a corollary of [`adjoint_nesty_duals`](proofs/adjoint/AdjointTop.v#L1736) through the inclusions [`straight_branchy`](proofs/adjoint/AdjointFoldy.v#L258), [`branchy_foldy`](proofs/adjoint/AdjointFoldy.v#L288), [`foldy_nesty`](proofs/adjoint/AdjointTop.v#L1730)), for bodies of straight lets and branches with no assignment in a branch; no `Admitted`. The proof found that adjoint-value lost the original value of an inout array (see `BUGS.md`, fixed in deed0ef) |
| M3, maps | done: [`afwd_map`](proofs/adjoint/AdjointBranch.v#L1636), [`arev_map`](proofs/adjoint/AdjointBranch.v#L1817) (`AdjointBranch.v`): the reverse loop replays the body at each index and transposes it from the adjoint of the element, the written array, dependent, having a zero tangent; [`adjoint_branchy_duals`](proofs/adjoint/AdjointTop.v#L1796) now covers maps at the end of the function; no `Admitted` |
| M4, scalar folds and tapes | done: [`afwd_fold`](proofs/adjoint/AdjointBranch.v#L2148), [`arev_fold`](proofs/adjoint/AdjointBranch.v#L2455) (`AdjointBranch.v`): the forward sweep pushes the state on a tape before each step when the reverse loop reads it ([`fold_tape`](proofs/adjoint/AdjointCorrect.v#L962)); the reverse loop pops it, replays the body and transposes it with the state as an extra owner, and the initial value receives the adjoint of the first state; [`adjoint_branchy_duals`](proofs/adjoint/AdjointTop.v#L1796) now covers scalar folds at the top level; no `Admitted` |
| M5, in-place array folds | done: [`afwd_fold_nbody`](proofs/adjoint/AdjointNBody.v#L1268), [`arev_fold_nbody`](proofs/adjoint/AdjointNBody.v#L1283) (`AdjointNBody.v`, with the pieces of `AdjointFold.v`): the forward sweep pushes on the tape of the array the element each step overwrites, when the reverse loop reads it; the reverse loop pops it back before replaying the step; [`adjoint_foldy_duals`](proofs/adjoint/AdjointTop.v#L1826) (`AdjointTop.v`) covers them at the top level, [`foldy`](proofs/adjoint/AdjointFoldy.v#L237) being a subclass of [`nesty`](proofs/adjoint/AdjointNesty.v#L25). Nests of any depth (`AdjointNBody.v`): an in-place fold whose steps end with a set, with an in-place fold of their state whose steps are again such bodies, or with the state itself ([`nbody`](proofs/adjoint/AdjointNBody.v#L21)); a state whose step ends with a fold or gives it back is never read by the reverse sweep ([`nbody_state_dead`](proofs/adjoint/AdjointNBody.v#L364), [`nbody_ret_dead`](proofs/adjoint/AdjointNBody.v#L444)), and each step's reverse sweep restores the state and pops what its inner fold pushed ([`tail_back`](proofs/adjoint/AdjointCorrect.v#L1056), [`arev_fold_nbody`](proofs/adjoint/AdjointNBody.v#L1283)); [`adjoint_nesty_duals`](proofs/adjoint/AdjointTop.v#L1736) covers them; no `Admitted`, only the axioms of the reals |
| M6, [`simplify`](modes/Simplify.v#L292) with tapes, the scoping of the adjoint code | done: [`simplify_correct_tapes`](proofs/passes/SimplifyCorrect.v#L2163) (`SimplifyCorrect.v`), simplify is correct on programs with tapes (a push or a pop writes its tape, in `simplify.elpi` as well); the scoping discipline of the adjoint code (`AdjointGood.v`: scope indexed by what the code reads, tapes declared before push and pop, bars declared before increment), for every body and value with no body class: [`agood_fwd`](proofs/adjoint/AdjointGoodFwd.v#L1092) (`AdjointGoodFwd.v`) and [`agood_adj`](proofs/adjoint/AdjointGoodRev.v#L1663) (`AdjointGoodRev.v`); at the top, [`adjoint_good`](proofs/adjoint/AdjointGoodTop.v#L122) and [`adjoint_nesty_simplified`](proofs/adjoint/AdjointGoodTop.v#L414) (`AdjointGoodTop.v`): the simplified adjoint function computes the gradient |
| M7, adjoint-value at the top, [`adjoint_mode_correct`](proofs/adjoint/AdjointMode.v#L43) | done: every well-formed program is in the class [`nesty`](proofs/adjoint/AdjointNesty.v#L25) ([`well_formed_nesty`](proofs/adjoint/AdjointClassify.v#L631), `AdjointClassify.v`, by parametricity from the typechecked instance; [`nesty`](proofs/adjoint/AdjointNesty.v#L25) quantifies its lets only over binders of their type), so [`adjoint_wf_duals`](proofs/adjoint/AdjointWf.v#L22) (`AdjointWf.v`) has no class premise; [`adjoint_mode_correct_from`](proofs/adjoint/AdjointModeProof.v#L74) (`AdjointModeProof.v`) derives the final statement (differentiability by [`duals_derive`](math/DualsDerive.v#L1491), the gradient as the transpose of df through the pairing identity in every direction), and [`adjoint_mode_correct`](proofs/adjoint/AdjointMode.v#L43) (`AdjointMode.v`) is proved from it, [`adjoint_nesty_simplified`](proofs/adjoint/AdjointGoodTop.v#L414) and [`well_formed_nesty`](proofs/adjoint/AdjointClassify.v#L631). `AdjointExamples.v` checks the class premise on 21 programs the tool accepts |

Proved in `AdjointCorrect.v`: the operations are linear in the tangents with
the spelled partial derivatives as coefficients; the forward sweep of each
operation computes its value (pushing the overwritten element on the tape of a
recorded storage); the reverse sweep of each operation transposes it, reading
only scalars that occur in it; typing and activity of the values (a value not
varied has a zero tangent); the let, with a fresh variable or updated in
place; returns, with the value adjoint-value leaves; the reverse sweep keeps the
value adjoint-value leaves ([`vo_kept`](proofs/adjoint/AdjointCorrect.v#L641): the reverse code of a straight value
writes only adjoints); [`asim_straight`](proofs/adjoint/AdjointCorrect.v#L3984).

Proved in `AdjointTop.v` ([`adjoint_simulates_duals`](proofs/adjoint/AdjointTop.v#L1002), Qed, for any body
simulated by [`asim_body`](proofs/adjoint/AdjointCorrect.v#L1224)): the arguments of the adjoint function laid out in
the store, the forward context, the prologue and the seed of each result (a
returned real; a written real, dependent or inout; a written array), the
reverse sweep from the owners (the arguments with an adjoint), the final
adjoints read back as the gradient, `<tangent v, yb> = <seed dx, g>`, and the
value in adjoint-value. Its hypothesis `length dx = in_dim x` was added, and
the Boolean arguments that carry an adjoint are excluded by well-formedness.

## Files

The files are grouped like the Elpi sources (`../elpi/`), plus the proofs;
each directory is mapped onto the logical name `ElpiDiff` (one `-R` per
directory in `_CoqProject`), so a module is `ElpiDiff.Syntax` whatever its
directory.

```
lang/            L0 and L1: Syntax Operations Anf Normalize WellFormed
analysis/        Atoms Activity Tbr Annotate
modes/           L2: Derivative Transform Tangent Adjoint Simplify Scoping
back/            L3 and printers: Target Lower Cxx Gallina Dump ToElpi
eval/            Domain Eval EvalAnf Exec, and Smooth (the partial semantics)
math/            Dot Euclidean DualsDerive RMat
proofs/passes/   Correctness AnfEquiv SimplifyCorrect
proofs/tangent/  TangentCorrect TangentLoops TangentGood TangentTop TangentMode
proofs/adjoint/  AdjointSpec ... AdjointMode, ModesAgree
top/             Adjudge (the driver), Main and MainMx (the short theorems)
```

| Rocq | Elpi | Contents |
|---|---|---|
| `Dot.v` | — | [`dotl`](math/Dot.v#L11), the dot product of two lists of reals, shared by the adjoint statements and proofs |
| `Syntax.v` | `syntax.elpi` (and the operators of `operations.elpi`) | L0: [`unary`](lang/Syntax.v#L20), [`binary`](lang/Syntax.v#L25), [`term`](lang/Syntax.v#L34), [`ty`](lang/Syntax.v#L61), [`role`](lang/Syntax.v#L69), [`result`](lang/Syntax.v#L78), [`definition`](lang/Syntax.v#L88), [`function`](lang/Syntax.v#L95), [`decl`](lang/Syntax.v#L101); [`written_role`](lang/Syntax.v#L105), [`varied_role`](lang/Syntax.v#L109) |
| `Anf.v` | the types of `anf.elpi` | L1 and L1ᵃ: [`atom`](lang/Anf.v#L17), `value`, `anf`, [`aresult`](lang/Anf.v#L38), [`adefinition`](lang/Anf.v#L42), [`afunction`](lang/Anf.v#L79), [`pexpr`](lang/Anf.v#L49); the annotations [`bare`](lang/Anf.v#L68) and [`ann`](lang/Anf.v#L70) |
| `Derivative.v` | the types of `derivative.elpi` | L2: [`dvar`](modes/Derivative.v#L17), [`dexpr`](modes/Derivative.v#L27), [`dsort`](modes/Derivative.v#L36), [`dstmt`](modes/Derivative.v#L42), [`dpass`](modes/Derivative.v#L62), [`dparam`](modes/Derivative.v#L69), [`dreturn`](modes/Derivative.v#L72), [`dbody`](modes/Derivative.v#L76), [`scoped`](modes/Derivative.v#L81), [`dfunction`](modes/Derivative.v#L108) |
| `Target.v` | `target.elpi` | L3: [`expr`](back/Target.v#L8), [`stmt`](back/Target.v#L15), [`cfunction`](back/Target.v#L32) |
| `Domain.v` | `numbers.elpi` | [`domain`](eval/Domain.v#L23); the reals ([`reals`](eval/Domain.v#L144)), for Elpi's floats; dual numbers over any domain ([`duals`](eval/Domain.v#L213)) |
| `Eval.v` | `eval.elpi` | [`val`](eval/Eval.v#L19); the evaluator of L0 ([`eval`](eval/Eval.v#L110), [`eval_function`](eval/Eval.v#L159)) |
| `Smooth.v` | — | the partial semantics of Abadi and Plotkin: the domain [`smooth_reals`](eval/Smooth.v#L43), the predicate [`defined`](eval/Smooth.v#L50) |
| `EvalAnf.v` | `eval-anf.elpi` | the evaluator of L1 and L1ᵃ ([`aeval`](eval/EvalAnf.v#L28), [`aeval_function`](eval/EvalAnf.v#L77)) |
| `Exec.v` | `exec.elpi` | the evaluator of L2 ([`exec`](eval/Exec.v#L117), [`exec_dfunction`](eval/Exec.v#L194)) |
| `Operations.v` | the table of `operations.elpi` | [`operation1`](lang/Operations.v#L28), [`operation2`](lang/Operations.v#L65) (the rows, first row or first match), [`extra_arguments`](lang/Operations.v#L42), [`partial1`](lang/Operations.v#L86), [`partial2`](lang/Operations.v#L104), [`unary_name`](lang/Operations.v#L121), [`binary_name`](lang/Operations.v#L130) |
| `Normalize.v` | the pass of `anf.elpi` | [`normalize`](lang/Normalize.v#L87) (L0 to L1: [`norm`](lang/Normalize.v#L21), [`norm_body`](lang/Normalize.v#L47), [`normalize_definition`](lang/Normalize.v#L61)), [`expressible`](lang/Normalize.v#L83), [`declarations`](lang/Normalize.v#L92) |
| `WellFormed.v` | `well-formed.elpi` | [`diagnostic`](lang/WellFormed.v#L20); [`well_formed`](lang/WellFormed.v#L403), [`typecheck`](lang/WellFormed.v#L143), `typecheck_value`, `type_of`, `occurs`, [`reads_around_inner_loop`](lang/WellFormed.v#L128) |
| `Atoms.v` | the atom sets and `atoms-of` of `anf.elpi` | [`avar`](analysis/Atoms.v#L17) (the variables of the analyses), [`same_term`](analysis/Atoms.v#L24), [`atom_member`](analysis/Atoms.v#L32), [`atom_remove`](analysis/Atoms.v#L35), [`atom_union`](analysis/Atoms.v#L40), `atoms_of_*` |
| `Activity.v` | `activity.elpi` | [`varied`](analysis/Activity.v#L16), [`varied_value`](analysis/Activity.v#L21), `varied_anf`, [`fold_varied`](analysis/Activity.v#L41), [`let_binder`](analysis/Activity.v#L47), [`fold_binders`](analysis/Activity.v#L50) |
| `Tbr.v` | `tbr.elpi` | [`sweep`](analysis/Tbr.v#L19); [`needs`](analysis/Tbr.v#L40), `value_needs`, [`read_by`](analysis/Tbr.v#L30), `records`, `records_in`, [`state_live`](analysis/Tbr.v#L120) |
| `Annotate.v` | `annotate.elpi` | [`annotate`](analysis/Annotate.v#L134) (L1 to L1ᵃ), in two traversals |
| `Transform.v` | the helpers of `derivative.elpi` | `tvar` (the variables of the transformations), [`sbind`](modes/Transform.v#L46), [`sflatten`](modes/Transform.v#L55), [`spell`](modes/Transform.v#L63), [`dot`](modes/Transform.v#L88), [`bar`](modes/Transform.v#L95), [`scale`](modes/Transform.v#L101), [`sum`](modes/Transform.v#L109), [`with_storage`](modes/Transform.v#L138), the opening of binders, [`with_arguments`](modes/Transform.v#L190), `type_of` |
| `Tangent.v` | `tangent.elpi` | `tangent` (L1ᵃ to L2): [`tan`](modes/Tangent.v#L100), `tan_value`, [`tangent_result`](modes/Tangent.v#L45), … |
| `Dump.v` | the printer of L2 in `dump.elpi` | [`pr_dfunction`](back/Dump.v#L105): the lines of `dump -- derivative <mode>` |
| `Adjoint.v` | `adjoint.elpi` | [`adjoint`](modes/Adjoint.v#L315) (L1ᵃ to L2), modes [`adjoint`](modes/Adjoint.v#L315) and `adjoint-value`: [`prim`](modes/Adjoint.v#L141) and `fwd_value`, then [`adj`](modes/Adjoint.v#L203) and `rev_value` |
| `Simplify.v` | `simplify.elpi` | [`simplify`](modes/Simplify.v#L292) (L2 to L2′): [`simplify_expr`](modes/Simplify.v#L60), [`simplify_stmts`](modes/Simplify.v#L158), `fuse`, with a fuel |
| `Lower.v` | `lower.elpi` | [`lower`](back/Lower.v#L90) (L2′ to L3), the counter of the names threaded; [`lower_all`](back/Lower.v#L100), the functions of a file |
| `Cxx.v` | `cxx.elpi` | [`function_string`](back/Cxx.v#L99), [`header_string`](back/Cxx.v#L111): the C++ text |
| `Gallina.v` | `gallina.elpi` | [`gallina_file`](back/Gallina.v#L379): the derivative programs after simplification as Gallina, for CertiRocq (assignments threaded as lets, loops `for_up`/`for_down`, reals primitive floats) |
| `Adjudge.v` | the driver of `adjudge.elpi` | [`mode`](top/Adjudge.v#L16), [`check`](top/Adjudge.v#L26), [`differentiate`](top/Adjudge.v#L31), [`transform`](top/Adjudge.v#L39), [`main`](top/Adjudge.v#L44): the header and the diagnostics of a case |
| `Scoping.v` | — | [`open_pairs`](modes/Scoping.v#L27), the opening of a generated function with the numbers simplify and the evaluator use; `good`, the scoping discipline of L2 |
| `SimplifyCorrect.v` | — | theorem 2: [`simplify_correct_tapes`](proofs/passes/SimplifyCorrect.v#L2163) |
| `Correctness.v` | — | [`parametric`](proofs/passes/Correctness.v#L73) (PHOAS relations of L0); [`normalize_correct`](proofs/passes/Correctness.v#L206), [`annotate_correct`](proofs/passes/Correctness.v#L292) |
| `AnfEquiv.v` | — | [`anf_eq`](proofs/passes/AnfEquiv.v#L33), the relation of two instances of L1; [`normalize_parametric`](proofs/passes/AnfEquiv.v#L211) |
| `Euclidean.v` | — | [`Rn`](math/Euclidean.v#L66), R^n as a normed module of Coquelicot; vectors and lists |
| `DualsDerive.v` | — | theorem 3: the domain of the functions of a point with their derivative; [`value_of`](math/DualsDerive.v#L1305), [`dual_args`](math/DualsDerive.v#L1315); [`duals_derive`](math/DualsDerive.v#L1491) |
| `TangentCorrect.v` | — | theorem 1, the simulation: [`pv`](proofs/tangent/TangentCorrect.v#L147), the record of the four instances; the invariants ([`static_ok`](proofs/tangent/TangentCorrect.v#L165), [`store_ok`](proofs/tangent/TangentCorrect.v#L178), [`ctx_ok`](proofs/tangent/TangentCorrect.v#L231)); the cases of returns, lets, operations, branches |
| `TangentLoops.v` | — | the loops of the simulation (map, scalar fold, in-place fold); [`simulation`](proofs/tangent/TangentLoops.v#L717) |
| `TangentGood.v` | — | the scoping discipline of the tangent code: [`scoping`](proofs/tangent/TangentGood.v#L1182) |
| `TangentTop.v` | — | the layout of the tangent function (`seed`, `tangent_inputs`, [`tangent_inputs_with`](proofs/tangent/TangentTop.v#L241), `tangent_output`); [`tangent_simulates_duals_with`](proofs/tangent/TangentTop.v#L690), [`tangent_simulates_duals`](proofs/tangent/TangentTop.v#L1151) |
| `TangentMode.v` | — | [`tangent_mode_correct_with`](proofs/tangent/TangentMode.v#L140), [`tangent_mode_correct`](proofs/tangent/TangentMode.v#L179) |
| `AdjointSpec.v` | — | the layout of the adjoint function: [`adjoint_inputs`](proofs/adjoint/AdjointSpec.v#L50) (primal arguments, initial adjoints xb or the seed yb, the seed of a returned value), [`adjoint_output`](proofs/adjoint/AdjointSpec.v#L105) (the gradient: final minus initial adjoints), [`value_given`](proofs/adjoint/AdjointSpec.v#L87) |
| `AdjointNBody.v` | — | in-place loops of any depth: the class [`nbody`](proofs/adjoint/AdjointNBody.v#L21) (ops and reads ending with a set, an inner in-place fold on the state, or the state), [`afwd_fold_nbody`](proofs/adjoint/AdjointNBody.v#L1268), [`arev_fold_nbody`](proofs/adjoint/AdjointNBody.v#L1283), [`nbody_asim`](proofs/adjoint/AdjointNBody.v#L2038) |
| `AdjointClassify.v` | — | the classification: [`well_formed_nesty`](proofs/adjoint/AdjointClassify.v#L631), every well-formed function has its opened body in [`nesty`](proofs/adjoint/AdjointNesty.v#L25), through a second pv instance opened at fresh binders ([`fpv`](proofs/adjoint/AdjointClassify.v#L29)) and related to the target by [`hinv`](proofs/adjoint/AdjointClassify.v#L34) |
| `AdjointGood.v`, `AdjointGoodFwd.v`, `AdjointGoodRev.v` | — | the scoping discipline of the adjoint code and its proof for every body: [`agood_fwd`](proofs/adjoint/AdjointGoodFwd.v#L1092), [`agood_adj`](proofs/adjoint/AdjointGoodRev.v#L1663) |
| `AdjointWf.v` | — | [`adjoint_wf_duals`](proofs/adjoint/AdjointWf.v#L22): the adjoint simulation for every parametric, well-formed function |
| `AdjointMode.v` | — | theorem [`adjoint_mode_correct`](proofs/adjoint/AdjointMode.v#L43): where f is defined, for every tangent dx, <df (seed dx), yb> = <seed dx, g>, and adjoint-value gives the value of f back (unless f writes an inout argument) |
| `ModesAgree.v` | — | `tangent_code`, [`adjoint_code`](proofs/adjoint/ModesAgree.v#L95); [`filterdiff_locally_unique`](proofs/adjoint/ModesAgree.v#L73) (a Fréchet derivative is unique); corollary [`adjoint_tangent_agree`](proofs/adjoint/ModesAgree.v#L105) |
| `Main.v` | — | the final theorems in short form: [`derivative_exists`](top/Main.v#L83), [`tangent_correct`](top/Main.v#L93), [`adjoint_correct`](top/Main.v#L110), [`adjoint_value_correct`](top/Main.v#L127), [`modes_agree`](top/Main.v#L140) |
| `RMat.v` | — | Stdlib `R` as a mathcomp `comRingType` (Hierarchy-Builder), with the axiom `constructive_indefinite_description` for the choice structure; used by `MainMx.v` only |
| `MainMx.v` | — | the Jacobian `J f x df` and [`adjoint_jacobian`](top/MainMx.v#L45) (g = Jᵀ yb) |
| `AdjointExamples.v` | — | non-vacuity: the accepted reference cases proved to be in the class of [`adjoint_nesty_duals`](proofs/adjoint/AdjointTop.v#L1736) |
| `AdjointModeProof.v` | — | [`adjoint_mode_correct_from`](proofs/adjoint/AdjointModeProof.v#L74): [`adjoint_mode_correct`](proofs/adjoint/AdjointMode.v#L43) from the simplified adjoint corollary |

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
  2020, see [References](#references)), where a comparison of two equal reals is undefined ([`smooth_reals`](eval/Smooth.v#L43),
  in `Smooth.v`). [`reals`](eval/Domain.v#L144) and [`duals`](eval/Domain.v#L213) never refuse: the evaluators of Elpi are
  mimicked as before.
- **Numbers.** Elpi's floats become the reals of Rocq (`R`); a literal, a
  string as in Elpi (`"0.9"`, `"13.0 / 12.0"`), is read exactly, as a rational
  number. Elpi's `int` becomes `Z`.
- **Names.** The constructors keep their Elpi names, capitalized (`num` →
  `Num`, `op1` → `Op1`); the prefixes `a-` and `d-` become `A` and [`D`](top/Main.v#L43)
  (`a-let` → `ALet`, `d-for-back` → `DForBack`); the three reserved words of
  Rocq take an underscore (`set` → `Set_`, `let` → `Let_`, [`function`](lang/Syntax.v#L95) →
  `Function_`). A predicate keeps its name with `_` for `-` (`eval-function` →
  [`eval_function`](eval/Eval.v#L159)).
- **Passes.** An Elpi pass that opens a binder with a hypothesis relating it
  to its image (`as-atom x a` in [`normalize`](lang/Normalize.v#L87)) instantiates, in PHOAS, the
  variables of its input with the terms of its output: [`normalize`](lang/Normalize.v#L87) takes a
  `term (atom V)`, so a source variable is its atom. A continuation-passing
  predicate (`norm T K R`) becomes a function taking its continuation.
- **Hypotheses on variables.** Where Elpi opens a binder with hypotheses on
  its variable (`of x T`, `argument x N R` in `well-formed`), the variables are
  instantiated with the record of that information ([`vinfo`](lang/WellFormed.v#L25)), whose identity,
  numbered in order, is what Elpi's [`same_term`](analysis/Atoms.v#L24) and `occurs` compare.
- **A pass whose input and output need different variables.** [`annotate`](analysis/Annotate.v#L134)
  reads its input with the variables of the analyses ([`avar`](analysis/Atoms.v#L17): an identity and
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
  functions of a file: [`lower`](back/Lower.v#L90) threads the counter.
- **Relations queried in several modes.** [`operation2`](lang/Operations.v#L65) has several rows per
  operator and a cut on the first: the table is kept as rows, with one
  function per use ([`operation2`](lang/Operations.v#L65), the first row; [`operation2_typed`](lang/Operations.v#L70), the
  first row matching given operand types).
- **One declaration per type.** [`comparison`](lang/Operations.v#L78), defined in `activity.elpi` from
  the operations table, is in `Operations.v`, with the same definition, so that
  the evaluators use it too. A Rocq inductive is declared in one place:
  the operators of `operations.elpi` are in [`unary`](lang/Syntax.v#L20) and [`binary`](lang/Syntax.v#L25) with
  `unknown1` and `unknown2` of `syntax.elpi`; `v-tape` of `exec.elpi` is in
  [`val`](eval/Eval.v#L19) with the values of `eval.elpi`; the key `returned` of `exec.elpi` is a
  constructor of the keys of the store, next to the variables.


## Checking against Elpi

`~/claudeExp/elpi/tools/rocqtest.py` (outside the repository, with the reference
cases) prints the functions of every case as Rocq terms (`torocq.elpi`), and
compares what Rocq computes with what Elpi prints: the diagnostics, and the
derivative programs printed by [`pr_dfunction`](back/Dump.v#L105) against `dump -- derivative|simplified
<mode>`, and the complete C++ headers against those [`main`](top/Adjudge.v#L44) writes, for the three
modes: 141 comparisons on the reference cases, all identical, line for line and
character for character.

## References

Also in [../paper/](../paper/README.md), with a BibTeX file.

- Martín Abadi and Gordon D. Plotkin. *A Simple Differentiable Programming
  Language*. Proc. ACM Program. Lang. 4, POPL (2020), 38:1–38:28.
  [doi:10.1145/3371106](https://doi.org/10.1145/3371106),
  [arXiv:1911.04523](https://arxiv.org/abs/1911.04523).
  Its partial semantics, where a comparison of two equal reals is undefined,
  is the one of the Rocq proofs: [`smooth_reals`](eval/Smooth.v#L43) and [`defined`](eval/Smooth.v#L50) in
  [Smooth.v](eval/Smooth.v), the hypothesis that `f` is defined at `x` of
  the main theorems.
- Alexey Radul, Adam Paszke, Roy Frostig, Matthew J. Johnson and Dougal
  Maclaurin. *You Only Linearize Once: Tangents Transpose to Gradients*. Proc.
  ACM Program. Lang. 7, POPL (2023), 1246–1274.
  [doi:10.1145/3571236](https://doi.org/10.1145/3571236),
  [arXiv:2204.10923](https://arxiv.org/abs/2204.10923).
  Reverse mode as forward mode, then partial evaluation with respect to the
  primal input (the residual program is linear in the tangents), then
  transposition of that linear program: the compiler view of the adjoint, a
  possible structure for the adjoint pass and its proof (tangent correct,
  partial evaluation preserves the semantics, the to-be-recorded analysis
  keeps the coefficients the reverse sweep reads, transposition is adjoint for
  every linear program).
- Laurent Hascoët, Uwe Naumann and Valérie Pascual. *"To be recorded"
  analysis in reverse-mode automatic differentiation*. Future Generation
  Computer Systems 21(8) (2005), 1401–1417.
  [doi:10.1016/j.future.2004.11.009](https://doi.org/10.1016/j.future.2004.11.009);
  free technical report INRIA RR-4856 (2003) on HAL,
  [inria-00071727](https://inria.hal.science/inria-00071727v1).
  The to-be-recorded analysis of Tapenade, which `tbr.elpi` follows: which
  values the reverse sweep reads and must therefore be recorded.
