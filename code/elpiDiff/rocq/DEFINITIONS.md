# Definitions of the elpiDiff Rocq development

A glossary of the definitions of the files of `_CoqProject`, in that order.
Its purpose is to let a reader understand the statements of the lemmas
without opening the definitions. The first part explains the concepts that
recur in the statements. The second part goes through the files one by one.

Notation used below: `V` is a type of PHOAS variables; `k` is the next
identity a pass gives to a binder; `c` is the number of the next variable of
the generated code; `s`, `s1`, `s2`, `s3` are stores of the L2 evaluator;
`L` is the list of variables in scope (of type `pv`); `O` is a list of owners.

---

## Key concepts

### The languages and PHOAS

- **L0** (`term`, Syntax.v) is the source language. **L1** (`anf V bare`,
  Anf.v) is its A-normal form: every intermediate value is named by a let, and
  an operation applies to atoms only. **L1ᵃ** (`anf V ann`) is L1 with the
  annotations of the analyses. **L2** (`dstmt`, Derivative.v) is the
  imperative derivative IR the transformations produce, and **L2′** is the
  same IR after `simplify`. **L3** (`stmt`, Target.v) is first-order C++.
- **PHOAS.** A term is parameterized by the type `V` of its variables, and a
  binder is a Rocq function (`Let_ e (fun x => b)`). A closed program is
  `forall V, …` (`fdef`, `afdef`, `dfbody`). Each pass *instantiates* the
  program at the type of variables it needs:
  - the evaluators instantiate it at values (`val N`);
  - `normalize` instantiates it at `atom V`;
  - `well_formed` instantiates it at `vinfo` (identity, type, argument name and role);
  - the analyses and `annotate` instantiate it at `avar` (identity, varied flag);
  - `tangent` and `adjoint` instantiate it at `tvar V` (everything the transformations know of a variable);
  - the evaluator of L2 instantiates it at `nat`, `simplify` at `nat * V`, and the proofs at `W = nat * nat`.
- **Opening a binder at an identity.** To look inside a binder, a pass applies
  it to a variable numbered `k` (`anon k`, `fresh k`, `let_binder k e`,
  `pfresh k`, `opened k`) and goes on at `S k`. For this reason most analyses
  take a `k` argument.

### Parametricity: relating the instances

Nothing in Rocq forces the instances `fdef f V1` and `fdef f V2` to be the
same term. The proofs therefore relate them explicitly.
- `term_equiv G t1 t2` (L0, Correctness.v) and `anf_eq G b1 b2` /
  `value_eq G e1 e2` / `atom_eq G a1 a2` (L1, AnfEquiv.v) say that two
  instances are the same term, where `G : list (V1 * V2)` pairs the variables
  in scope that correspond. A binder relates its two bodies on any pair added
  to `G`.
- `parametric f` says that any two instances of the source are related.
  `normalize_parametric` transfers this property to L1.

### The `pv` record and the graphs `gA gW gT gD` (TangentCorrect.v)

The simulation proofs use one more instance of the L1 program, at
`pv`, a record that bundles what each pass knows of one variable:

| field | type | meaning |
|---|---|---|
| `pa` | `avar` | the variable as the analyses see it (identity `aid`, varied flag `avaried`) |
| `pw` | `vinfo` | the variable as `well_formed` sees it (identity `vid`, type `vty`, argument `varg`) |
| `pt` | `tvar W` | the variable as the transformations see it (stored variable, dot, bar, recorded, …) |
| `pd` | `val (dual R)` | its value in the dual-number evaluation (primal value and tangent) |
| `pn` | `nat` | the number of the variable of the generated code that stores it |

- `stored p := DBound (pn p, pn p)` is the variable of the generated code
  that holds `p`.
- `gA L`, `gW L`, `gT L` and `gD L` are the lists
  `map (fun p => (p, pa p)) L`, and the same with `pw`, `pt` and `pd`. They
  are the contexts `G` that relate the `pv` instance to the instances of the
  analyses (A), of well_formed (W), of the transformation (T) and of the
  dual evaluator (D).
- A simulation lemma therefore starts with hypotheses such as
  `anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD`.
  They say that `bA`, `bW`, `bT` and `bD` are the four instances of the
  `pv` body `bP`, with the variables of `L` mapped by the four projections.
  Similarly, `amap pw a` maps an atom over `pv` to the corresponding
  `vinfo` atom.
- `static_ok k p` holds of every variable in scope, independently of the
  store:
  - the identities agree (`aid = vid`) and are below `k`;
  - `pt` stores the variable in `stored p`;
  - the types and the varied/dot flags agree;
  - a varied variable is a real or an array;
  - `pd` has the declared type, and its tangent is zero when the variable is
    not varied (the soundness of the activity analysis).

### The store of L2 and the numbering of the generated variables

- The evaluator of L2 (`exec`) threads a `store`, which is a list of
  `(key, val)` pairs. A `key` is `KVar v` for a variable `v : dvar nat`
  (`DBound n`, `DotOf v`, `BarOf v`, `TapeOf v`, `ResultVar`), or `Returned`.
- In the proofs, the generated code is instantiated at `W = nat * nat`, and
  `open_pairs sc c` opens its binders with `(c, c)`, `(c+1, c+1)`, …. It
  returns the opened value and the next number `c'`. This is why a lemma
  statement contains `let '((ss, …), c') := open_pairs (tan …) c in …`, which
  reads "the code the pass generates, with its fresh variables numbered from
  `c` to `c'`".
- `consistent v`: the two numbers of every `DBound (i, j)` inside `v` are
  equal. This holds of every variable opened by `open_pairs`.
- `keyv v := KVar (out_dvar nat v)` is the store key of a `W` variable.
  `xev s e` evaluates an expression and `run ss s` executes a block, both
  over the reals, after `out_dvar`.
- `below c v`: the variable `v` (or the variable it is a dot, bar or tape of)
  was opened before `c`. "The keys opened before `c`" are the keys of the
  variables that existed before the code under study ran.
- `frame c ex s s'` (tangent): every consistent key opened before `c` keeps
  its value from `s` to `s'`, except the in-place storage `ex` and its dot.

### Places, owners and in-place storage

- `place` (WellFormed.v) says where a body sits: `Top` (the body of the
  function), `InBranch`, `ScalarBody` (the body of a map or of a scalar fold),
  or `ArrayBody index state` (the body of a fold that updates an array in
  place). `typecheck` refuses some constructs in some places. For example, a
  scalar fold is accepted only at `Top`, and a branch is refused inside
  `ArrayBody`.
- `pplace` (TangentCorrect.v) is the same over `pv`: `PTop`, `PBranch`,
  `PScalar`, `PArray ix sx` (index and state of the in-place loop).
  `wplace` converts a `pplace` to a `place`.
- `wP : option (atom pv)` is the written argument: the argument a `Writes`
  function stores into, if any.
- `owner wP pp` is the variable whose storage a body may update in place:
  - at `PTop`, the written argument when it is an array;
  - in `PArray ix sx`, the loop state `sx`;
  - `None` otherwise.

  `inplace wP pp := option_map stored (owner wP pp)` is the variable of the
  generated code that holds it. In lemma statements, `inplace wP pp` is the
  `ex` ("excepted") argument of the frame predicates.
- `not_in_loop pp` holds unless `pp` is `PArray _ _`, that is, outside the
  body of an in-place loop.
- `storage wP tail eP` (TangentCorrect.v) says where `with_storage` puts the
  value of a let:
  - `Some (stored a)` for an `ASet` on `a`;
  - the storage of the initial array for an in-place `AFold`;
  - the written argument for a map that ends the body (`tail`);
  - `None` (a fresh local) otherwise.

  "A value stored in place" means `storage … <> None`.
- `place_ok L pp`: for `PArray ix sx`, the index and the state are in scope,
  the index is an integer, the state is a varied array, and neither is an
  argument.

### Activity, usefulness and the two sweeps

- **varied** (Activity.v): a value depends on an independent argument.
  `avaried` is this flag on a variable, `varied_value` / `varied_anf` compute
  it for a value or a body, and `fold_varied` computes it for the state of a
  fold.
- **sweep** (Tbr.v): `Forward` is the forward sweep of the adjoint, which
  computes and records values. `Replay` is a recomputation inside a reverse
  loop or a branch, which records nothing.
- **cv** ("computes-value") is `true` in mode adjoint-value: the forward
  sweep also produces the value of the function.
- `needs cv m k b = (U, L)` is the to-be-recorded analysis:
  - `U` is the set of atoms that the value of `b` depends on through
    positions that carry a derivative (the *useful* ones);
  - `L` is the set of atoms that the adjoint code of `b` reads by value.

  `value_needs` computes the same for one active value: the reads of its
  reverse sweep, and the atoms its adjoint flows to.
- **active** = varied and useful. **computed** = the rest of the body reads
  the let (`L`), or, in the forward sweep, a fold in the let records.
  `records` / `records_in` say that a fold records something.
  `state_live` says that the reverse loop reads the state of a fold, so the
  state is pushed on a tape before each overwrite.
- These are stored as `LetAnn varied active computed` and
  `FoldAnn varied recorded records` (`recorded` is the result of
  `state_live`; `annotate` calls it `live`).
- In the proofs: `useful cv m k bA p` means that `p` is in `U`, and
  `tbr cv m k bA p` (to be recorded) means that `p` is in `L`. `vreads`,
  `vflows` and `vatoms` are the same memberships for the two components of
  `value_needs` and for `atoms_of_value`. `live_anf k bW p` /
  `live_value k eW p` mean that `p` occurs in the body or value (`occurs_*`
  of WellFormed.v). In other words, "live" means "read by the rest of the
  program".

### Transformation variables (`tvar`, Transform.v)

`tvar V` is what `tangent` and `adjoint` know of a source variable:
- `tstored`: the variable of the generated code that holds it;
- `tty`: its type;
- `targ`: its argument name and role, if it is an argument;
- `tvaried`, `tdot`, `tbar`: whether it is varied, has a tangent, and has an
  adjoint;
- `trecorded`: whether its storage is recorded on a tape;
- `tid`: an identity, kept for arguments (`Some (S pos)`) and for the
  `probe` (`Some 0`).

`with_storage` chooses the storage of a let. An array is updated in place,
in the loop state or in the written argument. Anything else gets a
`Fresh "t"` local.

### The tangent simulation (theorem 1)

- `sim_body bP` describes the tangent code of the body `bP`, assuming:
  - the four instances of `bP` are related;
  - the context is `ctx_ok`;
  - the body type-checks with type `ty` (a real or an array);
  - the dual evaluation gives `v`.

  Then the statements `ss` that `tan` generates satisfy:
  - they number their fresh variables from `c` to `c' >= c`;
  - their value and tangent expressions `ve`, `de` read only live variables
    or new ones (`res_vars`, `dot_vars`);
  - run from `s`, they reach `s'` with `frame c (inplace wP pp) s s'`;
  - `body_result` holds: `ve`/`de` evaluate to the primal and tangent of `v`
    for a real, and the in-place storage holds them for an array;
  - the value has type `ty`, and it is zero when the body is not varied.
- `sim_value eP` is the same for one value computed into the variable `n`:
  `n` holds the primal value, and `DotOf n` holds the tangent when the value
  is varied or stored in place.
- `ctx_ok L k c s wP pp live ty` is the invariant of the context. `sctx` is
  its part that does not mention the store. Its fields are listed under
  TangentCorrect.v below.

### The adjoint simulation: pairing and owners (AdjointCorrect.v)

The adjoint proofs follow one real number, the **pairing**: the sum, over the
storages that carry an adjoint, of the tangent of the variable stored there
times its adjoint in the store.
- `owners := list (val R * dvar W)`. Each entry is a tangent (from the dual
  evaluation in a direction `dx`) and a storage.
- `barv s n := store_get s (keyv (BarOf n))` is the adjoint of the storage
  `n`.
- `inner t b` is `t * b` for reals and the dot product for arrays.
  `shaped t b` says that the adjoint `b` has the shape of the tangent `t`.
- `pairing O s := Σ_{(t, n) ∈ O} inner t (barv s n)`.
- `oset O n t` replaces the tangent recorded for the storage `n`.
  `oput O n t` does the same when `n` is already an owner, and otherwise adds
  `(t, n)`. This means "the storage `n` now holds a variable of tangent `t`".
- Transposing `x = e` moves the adjoint of `x` to the operands of `e`, which
  keeps the pairing. Hence the conclusions:
  - `pairing O s3 = pairing (oput O n (tangent ve)) s2` for a value (`asim_rev`);
  - `pairing O s3 = result_pairing O ty ex v se s2` for a body (`asim_body`).

  `result_pairing` is the pairing of `O` plus the tangent of a real result
  times the seed `se`. For an array result left in the storage `ex`, it is
  the pairing with that storage's tangent replaced by the result's.

### The adjoint contexts `actx`, `sctx`, `rctx`

- `actx L k c s wP pp live tb ty` is the context at the start of the forward
  sweep. It contains:
  - `a_sctx`: the store-independent facts (`sctx`);
  - `a_bar`: a variable has an adjoint iff it is varied;
  - `a_store`: every `tb` (to-be-recorded) variable has its primal value in
    `s`;
  - `a_tape`: every recorded variable has a tape;
  - `a_owner`: the owner's storage holds its primal value when outside a loop
    or when the owner is `tb`;
  - `a_tid`: outside a loop, the owner has an identity (it is an argument).
- `rctx L c wP pp O use s` is the context at the start of the reverse sweep:
  - `r_nodup`: the storages of `O` are distinct;
  - `r_shape`: their adjoints are shaped;
  - `r_below`: they are opened before `c`;
  - `r_useful`: every useful, varied variable in scope is an owner with its
    tangent;
  - `r_value`: an owner entry of a useful variable carries its tangent;
  - `r_owner`: the in-place owner is an owner with its tangent;
  - `r_args`: an argument is varied iff its role is varied;
  - `r_written`: the written argument has a written role.

### Frames of the adjoint code

- `fwd_frame c ex vo s s'`: the forward sweep leaves unchanged every
  consistent key opened before `c`, except tapes, the in-place storage `ex`,
  and the target of the value in adjoint-value (`vo_target vo`).
- `rev_frame c ex O s s'`: the reverse sweep leaves unchanged every key opened
  before `c`, except tapes, `ex`, and the adjoints of the owners in `O`.
  `rev_frame_x … n …` additionally excepts the value's own storage `n` (a
  fold restores its state).
- `tkeep c ex s s'`: tapes stay tapes (`tapes_kept`), and the tapes of
  variables opened before `c` keep their contents, except the tape of `ex`
  (`tapes_same`).
- `agree_prim c' ex s1 s2`: the primal keys and the tapes opened before `c'`
  are the same in `s1` (end of the forward sweep) and `s2` (start of the
  reverse sweep). The argument `ex` is not used in the body of the
  definition.
- `same_ex pp wP s s'`: outside a loop, the storage of a varied owner (an
  inout array) has the same value in `s` and `s'`.
- `vo : option (aresult (tvar W))` is what adjoint-value must output. It is
  `None` in mode adjoint or in a replay. `vo_target vo` is where the output
  goes: `ResultVar`, or the storage of a dependent written argument.
  `vo_result` says that the target holds the primal result after the forward
  sweep, and `vo_kept` says that the reverse sweep does not change it.
- `seed_ok c ty se s`: the seed expression reads keys opened before `c`, and
  it is a real for a real body. `seed_value` is its value.

### `asim_body`, `asim_fwd`, `asim_rev`, `psim_body`

- `asim_body cv bP` is the adjoint simulation of a body. It assumes:
  - the four instances are related;
  - `actx` holds with `live = live_anf k bW` and `tb = tbr cv m k bA`;
  - the body type-checks with type `ty`, and the dual evaluation gives `v`;
  - side conditions on the sweep: in `Forward` the place is `PTop` and `vo`
    agrees with `cv`; in `Replay` the place is not `PTop`; and so on.

  The code `(fw, rv)` that `adj … m … se` generates then satisfies:
  - `fw` runs from `s` to `s1`, with `fwd_frame`, `tkeep`, and `vo_result`
    in `Forward`;
  - for every `s2` and `O` with `agree_prim`, `rctx … O (useful …) s2`,
    `seed_ok`, `tapes_ok`, and (inside an in-place loop) `tail_tape`, the
    code `rv` runs from `s2` to `s3`, with `vo_kept`, `same_ex`, `tkeep`,
    `rev_frame`, the owners still shaped, and
    `pairing O s3 = result_pairing … s2`.
- `asim_fwd cv eP` covers the forward code (`fwd_value`) of one value
  computed into `n`. When `n` must be recorded, a tape is present. The code
  stores the primal value in `n`, with `fwd_frame c (Some n) None` and
  `tkeep`. In `Forward` outside a loop, the tape of a fold is as `fold_tape`
  says.
- `asim_rev cv eP` covers the reverse code (`rev_value`) of one varied value.
  It assumes:
  - the values its reverse sweep reads are in `s2`;
  - `rctx … O (vflows …) s2`;
  - a fresh storage `n` is not already an owner;
  - tapes are present (`tapes_ok`), with the contents `fold_tape` gives;
  - (outside a loop) the in-place storage holds the owner's primal value.

  Under these assumptions:
  - no primal key opened before `c` other than `n` changes;
  - the in-place storage is restored, or left unchanged;
  - `tkeep` and `rev_frame_x` hold, and the owners stay shaped;
  - `pairing O s3 = pairing (oput O n (tangent ve)) s2`.

  `asim_rev0` is an earlier, weaker form used for the operations: it reads
  only the scalars it needs.
- `psim_body cv bP` (AdjointBranch.v) covers the forward computation of a
  branch body by `prim`. Its value expression evaluates to the primal value.
  The tape of the owner's storage follows `tape_step`, and the owner's array
  changes at most at the `set_index`.

### Recording folds: traces and tapes

- `fold_trace ev i n s` is the list of the states of a fold *before* each of
  its `n` steps, starting at index `i` from state `s`.
- `set_index b` is the index (as evaluated) of the `ASet` that ends the body
  `b`.
- `body_pushes b st` is the list of elements that one step of an in-place
  fold pushes on the tape of its storage, from the state `st` before the
  step:
  - the element of `st` that the final set overwrites;
  - if the step ends with an inner in-place fold instead, the concatenation
    of the pushes of that fold's steps.

  `fold_pushes b z tr` concatenates `body_pushes` over the trace `tr`.
- `tail_fold_live cv k b` handles a body that ends with a chain of tail
  in-place folds. It returns `Some (state_live …)` of the innermost fold of
  the chain, and `None` when the body does not end with a fold.
  `fold_live cv k init b` is this value for the body of the fold, or the
  fold's own `state_live` when there is none.
- `fold_tape k eA eW eD s n` describes the tape of a fold value in the store
  `s`, with storage `n`:
  - for a scalar fold whose state is live, `TapeOf n` holds the reals of the
    trace, last first;
  - for an in-place fold that is `fold_live`, `TapeOf n` starts with
    `rev (fold_pushes …)`, followed by older contents, and `n` holds the
    final array.

  It is `True` for any other value.
- `ptail cP`: the continuation returns its own variable, so the let it
  continues is the tail of the body.
- `tail_tape k L b bA bD s n`: for every let of `b` that is the tail,
  `fold_tape` holds of its value, with the activity instance `bA` and the
  dual instance `bD` of `b` fixed: a let is followed only on the value it
  computes (`aeval_value` of its dual instance) and on its activity binder
  (`let_binder`). Inside an in-place loop, this is how the body receives the
  tape of the inner fold its step ends with.
- `tapes_ok L s`: every recorded variable in scope has a tape in `s`.

### Reading a statement: an example

The comment "Inside the body of an in-place loop, a value not stored in place
is no fold: a scalar recurrence is not typed there" is on:

```
Lemma fold_tape_in_loop L k wP tail ix sx eP eA eW eD te s n :
  value_eq (gW L) eP eW -> storage wP tail eP = None ->
  typecheck_value (option_map (amap pw) wP) (wplace (PArray ix sx)) tail k eW = (te, Ok) ->
  fold_tape k eA eW eD s n.
```

`eP` is the `pv` instance of a value and `eW` its well_formed instance. The
place `PArray ix sx` is the body of an in-place loop. The hypothesis
`storage … = None` says that the value is put in a fresh local, so it is not
stored in place. Under these hypotheses, `typecheck_value` refuses a scalar
fold at that place, so the value is not a fold, and `fold_tape` is `True`.

---

## The files

### Syntax.v: L0, the source language

It mirrors `syntax.elpi` in PHOAS. The constructors keep the Elpi names,
capitalized.

- `unary`: `Neg | Sin | Cos | Exp | Log | Sqrt | Pow k | Unknown1 s`, the unary operations; `Pow k` is x^k.
- `binary`: `Add | Sub | Mul | Divide | Lt | Le | Gt | Ge | Unknown2 s`; the comparisons are passive.
- `term V`: `Var x | Num s` (a real literal, spelled) `| Nat k | Op1 f a | Op2 f a b | Get a i | Set_ a i v` (a new version of `a` with `a[i]` replaced) `| Let_ e b | Ite c t e | Map lo hi b` (the array `[b i | lo <= i < hi]`) `| Fold lo hi init b` (`s := init; for i: s := b i s`).
- `ty`: `Real | Integer | Boolean | Array n` (an array of reals with a static extent).
- `role`: `Independent` (differentiated with respect to), `Dependent` (written and never read; its derivative is wanted), `Inout` (read then overwritten), `Passive`.
- `result V`: `Returns t` (the body's value is returned) or `Writes y` (it is stored in the argument `y`).
- `definition V`: `Arg n t r f` (one binder per argument, in the order of the C++ signature) or `Body r b`.
- `function` (record): `fname : string`, `fdef : forall V, definition V`. A closed source function.
- `decl`: `Decl n t r`, an argument as plain data.
- `written_role r`: `r` is `Dependent` or `Inout` (the function writes the argument).
- `varied_role r`: `r` is `Independent` or `Inout` (the argument carries a derivative on entry).

### Anf.v: L1 and L1ᵃ

These are the types of `anf.elpi`. They are indexed by the annotation type
`I` (`bare` for L1, `ann` for L1ᵃ). Values and bodies are mutually
inductive.

- `atom V`: `AVar x | ANum s | ANat k`.
- `value V I` (what a let binds): `AOp1 f a | AOp2 f a b | AGet a i | ASet a i v | AIte c t e` (branches are bodies) `| AMap lo hi b | AFold ann lo hi init b`.
- `anf V I` (a body): `ALet ann e b | ARet x`.
- `aresult V`: `AReturns t | AWrites y`.
- `adefinition V I`: `AArg n t r f | ABody r b`.
- `pexpr V`: a partial derivative as a nested expression over atoms: `PAtom a | PNum s | POp1 f a | POp2 f a b`.
- `bare`: `Bare`, no annotation (L1).
- `ann`:
  - `LetAnn varied active computed`, on a let: the value is varied; it is active (varied and useful); it is computed in its sweep;
  - `FoldAnn varied recorded records`, on a fold: the state is varied; it is recorded before each overwrite; the fold records something.
- `afunction I` (record): `afname`, `afdef : forall V, adefinition V I`.

### Derivative.v: L2, the derivative IR

This is an imperative language whose variables are bound at the head of the
function, in order of creation.

- `dvar V`: `DBound x` (bound by `Named`/`Fresh`) `| DotOf v` (its tangent) `| BarOf v` (its adjoint) `| TapeOf v` (the tape of its successive values) `| ResultVar` (the returned value).
- `dexpr V`: `DVar v | DReal s | DInt k | DAt a i | DOp1 f a | DOp2 f a b`.
- `dsort`: `DConstant t` (never reassigned) or `DMutable` (a real, reassigned or accumulated).
- `dstmt V`:
  - `DDefine s v e`: a variable and its initial value;
  - `DRealVar v`: a real assigned later in both branches;
  - `DTape v`: an empty tape;
  - `DAssign l e`, `DIncrement l e` (`+=`, the adjoint accumulation);
  - `DBranch c t e`;
  - `DFor i lo hi b` (upward) and `DForBack i lo hi b` (the same indices, downward);
  - `DPush t e`, `DPop t l` (restores the last recorded value into `l`);
  - `DReturn e`.
- `dpass`: `ByValue | ByRef` (written) `| ByCref` (read only) `| ByRefUnused` (the caller's storage, never accessed).
- `dparam`: `DParam p t v`. `dreturn`: `DReturnsReal | DVoid`. `dbody`: `DBody r params stmts`.
- `scoped V A`: `Named n f` (an argument with its C++ name) `| Fresh p f` (a local with a name prefix) `| Done a`. A value under the binders of its variables.
- `code V := scoped V (list (dstmt V))`.
- `dfunction` (record): `dfname`, `dfbody : forall V, scoped V (dbody V)`.

### Target.v: L3, C++ statements

First order, with names as strings. It is produced by `lower` and printed by
`cxx`.

- `expr`: `Id s | Lit s | At a i | Call f args` (an operator or a function).
- `stmt`: `Declare t n e | Allocate t n | Assign l e | Increment l e | Branch c t e | Loop i lo hi b | LoopBack i lo hi b | Push t e | Pop t e | Return e`.
- `cfunction`: `CFunction ret name args body`.

### Domain.v: domains of numbers

A domain is the record of the operations on its numbers. Every operation
returns an `option`. A comparison returns `option bool`, so that a domain
may refuse a tie.

- `domain N` (record): `dom_lit : string -> option N` (reads a literal), `dom_op1`, `dom_op2` (arithmetic), `dom_cmp : binary -> N -> N -> option bool`.
- `digit`, `read_digits`, `read_sign`, `read_decimal`, `strip`, `read_literal`: read a literal string exactly as a rational `Q`. The literal is an optional sign, digits, an optional fraction and an optional exponent, or the quotient of two such numbers (`"13.0 / 12.0"`).
- `real_lit`, `real_op1`, `real_op2`, `real_cmp`: the operations of the reals (`R`). `real_cmp` always answers.
- `reals : domain R`: the domain that stands for Elpi's floats.
- `dual N`: `Dual x dx`, a value and its tangent.
- In section `Duals` (over a domain `B`):
  - `dual_lit`: a literal with tangent 0;
  - `dual_partial1 f x y`: the derivative of `f` at `x`, where `y = f x`;
  - `dual_op1` and `dual_op2`: the value, and the tangent by the chain rule;
  - `dual_cmp`: compares the values in `B`;
  - `duals B : domain (dual N)`.
- Local notation `let* x := a in b`: the option bind.

### Eval.v: evaluator of L0

- `val N`: `VReal x | VInt k | VBool b | VArray xs | VTape xs` (a tape, last value pushed first).
- Notation `let* x := a in b`: the option bind, with a pattern.
- `nth_z k l`, `replace_nth k x l`, `replace_nth_z k x l`: list access and update at an integer index, `None` when out of range.
- `int_holds f x y`, `int_op2 f x y`: integer comparisons and arithmetic.
- `eval_op1 f a`, `eval_op2 f a b`: an operation on values. Two integers compute exactly. Two reals go through the domain, with `dom_cmp` when `comparison f` holds and `dom_op2` otherwise.
- `eval_map ev i n`: the reals `ev (VInt i) … ev (VInt (i+n-1))`.
- `eval_fold ev i n s`: the state after `n` steps from `s`.
- `count i j := Z.to_nat (j - i)`: the number of indices of `[i, j)`.
- `eval D t`: the big-step evaluator of L0 in the domain `D`. A binder is applied to the value of its variable.
- `eval_definition d args`: applies `d` to `args`. `eval_function f args := eval_definition (fdef f (val N)) args`. The result is the returned value, or the new value of the written argument.

### Smooth.v: the partial semantics of Abadi and Plotkin

- `smooth_op1`: fails for `Log`/`Sqrt` at `x <= 0` and for a negative power at 0.
- `smooth_op2`: fails on a division by 0.
- `smooth_cmp`: fails at a tie (equal operands).
- `smooth_reals : domain R`: the reals with these failures.
- `defined f args := exists v, eval_function smooth_reals f args = Some v`. The evaluation compares no equal reals and applies no operation where it is not differentiable.

### EvalAnf.v: evaluator of L1 and L1ᵃ

It is polymorphic in the annotation type `I`, since the annotations do not
change what a program computes.

- `aeval_atom D a`: the value of an atom (a literal is read through `dom_lit`).
- `aeval D b` / `aeval_value D e`: the evaluators of bodies and values. They are mutually recursive and use the operations of Eval.v.
- `aeval_definition`, `aeval_function`: apply a definition or function to its arguments.

### Exec.v: evaluator of L2

- `dvar_eqb`: equality of `dvar nat`.
- `key`: `KVar v | Returned` (where `DReturn` leaves its value). `key_eqb` is its equality.
- `store N := list (key * val N)`.
- `store_get`: the first binding of a key. `store_set`: updates a key in place, or appends it.
- `xeval D s e`: the value of an expression in the store `s`.
- `assign D s l v`: assigns `v` to a variable or to an element `x[i]`.
- `exec_up body i lo n s` / `exec_down body i hi n s`: run `body` `n` times, setting `i` to `lo, lo+1, …` / `hi, hi-1, …`.
- `exec D st s`, `exec_stmts D l s`: execute one statement or a block. `DRealVar` initializes to 0. `DIncrement` adds. `DPush` conses onto a tape, and `DPop` takes the head and assigns it. `DReturn` sets `Returned`.
- `exec_scoped D sc k args`: opens the binders with the numbers `k, k+1, …` and binds the parameters to `args`. It returns `(finals, rets)`: the final values of all the parameters, and `[v]` for a function returning `v` (`[]` otherwise).
- `exec_dfunction D f args := exec_scoped D (dfbody f nat) 0 args`.

### Operations.v: the operation table

- `ty_eqb`: equality of types. `z_to_string`: an integer in decimal.
- `operation1 f`: `Some (operand type, result type, C++ spelling)`, or `None` for an unknown operator.
- `extra_arguments f`: the literal arguments after the operand in the C++ call (the exponent of `pow`).
- `operation2_rows f`: the rows `(type1, type2, result, spelling)` of a binary operator, in order.
- `operation2 f`: the first row. It answers a query with unknown operand types.
- `operation2_typed f ta tb`: the result type and spelling of the first row matching the operand types.
- `comparison f`: the first row of `f` returns `Boolean`.
- `partial1 f a`: the derivative of `AOp1 f a` with respect to `a`, as a `pexpr`.
- `partial2 f a b`: the pair of derivatives of `AOp2 f a b` with respect to `a` and `b`.
- `unary_name`, `binary_name`: names for diagnostics, as Elpi prints them.

### Normalize.v: `normalize`, from L0 to L1

- `bind k := fun v => k (AVar v)`: turns a continuation on atoms into a binder.
- `norm t k`: continuation-passing A-normalization. The source is instantiated at `atom V`, so a source variable *is* its atom.
- `norm_body t := norm t ARet`: a body ended by its atom.
- `normalize_result r`: a written argument becomes `AWrites` of its atom. A written expression, which cannot occur on an expressible function, gives the literal 0.
- `normalize_definition d`: normalizes the body under the argument binders.
- `expressible_definition`, `expressible f`: the result of `f` is `Returns`, or `Writes (Var _)`.
- `normalize f : afunction bare`.
- `declarations d`: the arguments of an L1 definition as a `list decl`, with the binders opened at `unit`.

### WellFormed.v: the supported language, as a diagnostic

- `diagnostic`: `Ok | Error m`. `is_ok` tests it. `q s` quotes a name in a message.
- `vinfo` (record): `vid : nat` (the identity), `vty : ty` (the type), `varg : option (string * role)` (name and role of an argument).
- `anon k := VInfo k Real None`: a variable opened only to look into a binder.
- `of_atom a`: the type of an atom.
- `same_atom a b`: the same variable (same `vid`).
- `occurs_atom y a`, `occurs_anf y k b`, `occurs_value y k e`: the variable of identity `y` occurs. Inner binders are opened with `anon` from `k`.
- `is_tail b k`: the body `b` (a binder) returns exactly its own variable, that is, has the shape `x\ a-ret x`.
- `place`: `Top | InBranch | ScalarBody | ArrayBody index state` (see Key concepts).
- `written_decl d`: the declaration has a written role. `ty_is_array t`: `t` is an array type.
- `in_place_init written p tail init`: an in-place fold starts either from the written argument at the end of the function (`Top`, tail) or from the state of the enclosing in-place fold at the end of its body.
- `ends_with_fold k b`: `b` ends with a fold in tail position.
- `reads_before_tail s k b`: `b` reads the variable `s` before its tail let.
- `reads_around_inner_loop s k b`: both hold, that is, the body reads the state `s` before an inner in-place loop that ends it.
- `typecheck written p k b = (T, D)`: in place `p`, the body `b` has type `T`, or `D` explains why not. `typecheck_value written p tail k e` does the same for one value, where `tail` says that the let ends its body. This encodes all the restrictions: where maps, folds, sets and branches may appear, and what they may read.
- `well_formed_result decls r b k`: checks the result against the declarations (single written argument, `Dependent` not read, `Inout` read, …).
- `well_formed_definition decls k d`: opens the arguments as `VInfo k t (Some (n, r))`, then checks the result.
- `non_real_varied ds`: the first independent or inout argument that is neither a real nor an array.
- `well_formed f : diagnostic`: the whole check.
- `type_of e : option ty`: the type of a value in a well-formed body, annotated or not.

### Atoms.v: sets of atoms

- `avar` (record): `aid : nat` (the identity), `avaried : bool` (varied flag). These are the variables of the analyses.
- `same_term a b`: the same variable (same `aid`).
- `atom_member`, `atom_remove`, `atom_union`: sets of atoms as lists compared by `same_term`. `atom_union` adds no duplicates.
- `atoms_of_atom`, `atoms_of_atoms`, `atoms_of_anf k b`, `atoms_of_value k e`, `atoms_of_pexpr p`: the bound variables a term mentions, excluding its own binders.
- `fresh k := AV k false`: a variable opened to look into a binder.

### Activity.v: `varied`

- `varied a`: the atom is a varied variable.
- `varied_value k e`, `varied_anf k b`: the value or body depends on an independent argument. A comparison is never varied. A let binder is opened with its varied flag.
- `fold_varied k init b`: the state of a fold is varied when `init` is, or when one pass of the body from a passive state makes it varied.
- `let_binder k e := AV k (varied_value k e)`: the variable of `let e`.
- `fold_binders k init b := (AV k false, AV (S k) (fold_varied k init b))`: the index and the state of a fold.

### Tbr.v: to-be-recorded

- `sweep`: `Forward | Replay` (see Key concepts). `sweep_eqb` is its equality.
- `read_by a p`: the atoms that the partial derivative `p` reads, when the operand `a` is varied.
- `needs cv m k b = (U, L)`: U the useful atoms of `b`, L the atoms its adjoint code reads by value. A tail atom is in L only in the forward sweep with `cv`.
- `value_needs cv k e = (R, F)`: for an active value, R the atoms its reverse sweep reads, F the atoms its value depends on. Loop bodies and branches are analyzed in `Replay`.
- `records cv k e`: `e` is a fold whose state the reverse loop reads, or whose body contains a recording fold. `records_in cv k b`: some let of `b` records.
- `state_live cv k init b`: the state of the fold is in the L of its body (replayed). The state is then recorded before each overwrite.

### Annotate.v: from L1 to L1ᵃ

The closed input is traversed twice: once at `avar` to compute the
annotations, once at `V` to rebuild the term with them.

- `ltree`: `TLet a v rest | TRet`, and `vtree`: `TLeaf | TIte t e | TMap b | TFold a b`. The annotations in the shape of the lets, the folds and the inner bodies.
- `annotate_body_t cv m k b`: the annotation tree of a body transposed in sweep `m`:
  - `varied` is `varied_value`;
  - `active` is varied and useful;
  - `computed` is needed by the rest, or, in the forward sweep, a fold in the let records.
- `annotate_value_t cv k e`: the bodies inside a value are annotated in `Replay`. A fold gets `FoldAnn (fold_varied) (state_live) (records)`.
- `annotate_definition_t cv k d`: opens the arguments with `varied_role`, then annotates the body in `Forward`.
- `no_ann := LetAnn false false false`: the default annotation (never used on matching trees).
- `rebuild b t`, `rebuild_value e t`, `rebuild_definition d t`: the term over `V` with the annotations of the tree.
- `has_inout d dummy`: the definition has an `Inout` argument.
- `annotate_cv cv f := cv && negb (has_inout …)`: adjoint-value is annotated as adjoint when the function has an inout argument.
- `annotate cv f : afunction ann`.

### Transform.v: helpers of the transformations

- `tvar V` (record): `tstored`, `tty`, `targ`, `tvaried`, `tdot`, `tbar`, `trecorded`, `tid` (see Key concepts).
- `code := scoped V (list (dstmt V))`.
- `sbind s k`: the monadic bind of `scoped`. It keeps the binders of `s` followed by those of `k`.
- `sflatten ss`: concatenates a list of scoped blocks.
- `spell a`: an atom as an expression. A variable becomes `DVar (tstored x)`.
- `spell_partial p`: a partial derivative as an expression.
- `tvaried_atom a`, `tof a`: the varied flag and the type of an atom.
- `dot a`: `DVar (DotOf (tstored x))` when `x` has a tangent, `DReal "0"` otherwise.
- `bar a`: `Some (DVar (BarOf …))` when `x` has an adjoint, `None` otherwise.
- `scale p e`: `p * e`, simplified for `1` and `-1`. `sum es`: the sum of a list, `0` when empty.
- `probe`: a `tvar` with `tid = Some 0`, used to test the shape of a body.
- `is_tail b`: `b probe` returns the probe, that is, the shape `x\ a-ret x`.
- `is_written written a`: `a` is the written argument (compared by `tid`).
- `with_storage written e b k`: chooses the storage of `let e b` and passes it to `k` together with its recorded flag:
  - the array of an `ASet`;
  - the initial array of an in-place fold;
  - the written argument for a tail map;
  - otherwise `Fresh "t"`, not recorded.
- `open_let t n vr rec`: the `tvar` of a let stored in `n`. A varied value has a tangent and an adjoint.
- `open_fold vr t n i rec`: the index (in `i`) and the state (in `n`) of a fold.
- `open_index i`: the index of a map.
- `open_arguments d pos acc k` / `with_arguments d k`:
  - binds each argument with `Named`, its `tid` being `Some (S pos)`;
  - a varied role gives a tangent and an adjoint;
  - then calls `k` with the declarations and their variables, the result, the body, and the written argument.
- `type_of e : ty`: the type of a value, using the types the transformations know.

### Tangent.v: forward mode, L1ᵃ to L2

- `tangent_code := scoped V (list (dstmt V) * (dexpr V * dexpr V))`: statements, with the value and the tangent of the tail atom.
- `tangent_primal a`: the parameter of a primal argument. Integers and reals are passed by value, written arguments by reference, and other read arrays by const reference.
- `tangent_dot a`: the tangent parameter of a non-integer, non-passive argument (by value, const reference or reference).
- `tangent_result res v d`: where the result goes:
  - a returned real: its tangent goes in the reference parameter `DotOf ResultVar`, then `DReturn v`;
  - a written real is assigned along with its dot;
  - an array is written in place (no statement).
- `tangent_term a p`: `[p * dot a]` when `a` is varied, `[]` otherwise.
- `tan_ite`, `tan_map`, `tan_fold`: the statements for a branch, a map writing `n` and its dot element by element, and a scalar fold with its mutable state and dot.
- `tan written b`: the tangent code of a body. It returns the statements and the value and tangent of its tail.
- `tan_value written e t vr n`: computes `e` into `n`, and its tangent into `DotOf n` when `vr`. An in-place fold just runs its body in a `DFor`.
- `tangent_body args res b written`: the signature (primal parameters, then tangents, then the extra tangent of the result) and the statements.
- `tangent f : dfunction`, named `<f>_tangent`.

### Dump.v: printer of L2

- `ty_string`, `op1_string`, `op2_symbol`: the printed forms of types and operators.
- `var_name v`: `x`, `x_dot`, `x_bar`, `x_tape`, `result`.
- `dexpr_strings e`: the top-level form and the operand form (parenthesized when infix). `dexpr_string` is the first.
- `pass_word`, `param_text`: a parameter, as in `x: const ref real[3]`.
- `pr_stmt ind s`: the lines of a statement.
- `pr_scoped name s k`: names `Fresh` binders `prefix ++ number` from `k`.
- `pr_dfunction f`: the lines of `dump -- derivative <mode>`.

### Adjoint.v: reverse mode, L1ᵃ to L2

- `sweeps := list (dstmt V) * list (dstmt V)`: the forward sweep and the reverse sweep.
- `adjoint_primal cv a`: the parameter of a primal argument. A dependent argument is `ByRef` in adjoint-value and `ByRefUnused` otherwise. An inout array is passed by value.
- `adjoint_bar a`: the adjoint parameter of a non-integer, non-passive argument.
- `role_of a`, `stored_of a`: the role and the storage of an argument atom.
- `adjoint_seed res = (extra params, prologue, seed)`:
  - for a returned value, the parameter `BarOf ResultVar` is the seed;
  - for a written dependent real, the seed is its adjoint;
  - for a written inout real, the adjoint is copied into `BarOf ResultVar` and reset to 0;
  - for an array, there is no seed (`0`).
- `value_output vo x`: at the end of the forward sweep in adjoint-value, sends the value `x` to `ResultVar` or to the written dependent real.
- `bar_declaration t n`: `var real n_bar = 0` for a real.
- `contribution a p x`: `a_bar += p * x` when `a` has an adjoint.
- `tail_index b`: the index of the set that ends the body of an in-place fold.
- `rev_loop i lo hi pop mid (f, rv)`: `DForBack` over `pop ++ f ++ mid ++ rv` (restore, replay, then propagate).
- `fwd_fold i lo hi init live n r`: a scalar fold in the forward sweep. When `live`, a tape is declared and the state is pushed before each step.
- `let_ann a`, `fold_ann a`: the three flags of a `LetAnn` / `FoldAnn`.
- `prim written m b`: the primal computation of a body (recording when `m = Forward`), with the value of its tail.
- `fwd_value written m e t n rec`: computes `e` into `n`:
  - an `ASet` on a recorded storage pushes the overwritten element in `Forward`;
  - an in-place fold declares the tape when it writes the written argument and records.
- `adj written vo m b seed`: the forward and reverse sweeps of a body:
  - a let is computed (`fwd_value`) when its annotation says *computed*;
  - it is transposed (`rev_value`) when *active*;
  - the tail adds `seed` to the adjoint of the tail atom.
- `rev_value written vo e t n`: propagates `BarOf n` to the atoms of `e`:
  - an `ASet` moves the element's adjoint and zeroes it;
  - a branch is replayed then transposed;
  - a map or a fold becomes a reverse loop. A fold pops its state back when live.
- `adjoint_finish cv res params prologue (fwd, rev)`: the body: forward sweep, prologue, reverse sweep, and the return of `ResultVar` in adjoint-value.
- `inout_result res`: the function writes an inout argument.
- `adjoint_body cv args res b written`: the signature and the sweeps. `vo` is `Some res` in adjoint-value without inout.
- `adjoint cv f : dfunction`, named `<f>_adjoint` or `<f>_adjoint_value`.

### Simplify.v: L2 to L2′

- `W := nat * V`: the input is instantiated with pairs, a number (compared) and an output variable (kept).
- `dvar_eq a b`: compares the numbers.
- `is_lit s e`: `e` is the literal `s`.
- `simplify_op1`, `simplify_op2`, `simplify_expr`: algebraic identities (`x^1`, `x^0`, `- - x`, `0 *`, `1 *`, `-1 *`, `+ 0`, `- 0`), bottom-up.
- `mentions_expr v e`, `mentions v s`: `v` occurs (read or written) in an expression or a statement.
- `target v l`, `writes v s`: `s` assigns or accumulates into `v`.
- `replace_expr v l e`, `replace_stmt v l s`: substitute the literal `l` for `v`.
- `first_mention v ss`: splits a block at the first statement that mentions `v`.
- `simplify_stmts n ss`, `simplify_stmt n s`, `fuse n ss`: these use a fuel `n`, and leave the block as is when it runs out. `fuse`:
  - drops `+= 0`;
  - fuses a mutable initialized to 0 with its first accumulation;
  - removes unused definitions;
  - propagates literal constants.
- `size s`, `fuel ss := 2 * size + 10`: the fuel.
- `out_dvar`, `out_dexpr`, `out_dstmt`, `out_dparam`: from `W` to the output variables (drop the numbers).
- `simplify_scoped s k`: opens the binders with `(k, v)`, then simplifies the body.
- `simplify f : dfunction`.

### Scoping.v: the scoping discipline of L2

- `W := nat * nat`.
- `open_pairs s k`: opens a scoped value, the j-th binder with `(j, j)`. It returns the value and the next number.
- `consistent v`: the two numbers of each `DBound` agree.
- `expr_ok sc e`: every variable `e` reads is in the scope `sc`.
- `lhs_ok sc wr l`: `l` is a writable variable in `wr`, or an element of one with an index in scope.
- `good sc wr ss` (inductive) is the discipline:
  - every variable read is in scope;
  - every variable assigned is writable (a parameter or a mutable local);
  - every variable defined is new (not in `sc`) and consistent;
  - a `DDefine DMutable`, `DRealVar` or `DTape` adds its variable to `sc` and `wr`, and a constant adds it to `sc` only;
  - a loop index is new and visible only in the loop body.

### Lower.v: L2′ to L3

- `return_type`, `array_type`, `value_type`, `pass_string`, `param_string`: the C++ types and parameters (`T`, `std::array<T, n>`, `const T&`, `T& /*x*/`).
- `spelling1`, `spelling2`: the C++ spelling of an operator.
- `lower_expr`, `lower_stmt`: the translation. A real literal becomes `T(s)`, and a tape becomes a `std::vector<T>`.
- `lower_scoped name s k`: names the `Fresh` binders with a counter `k`, threaded across the functions, and returns the next value.
- `lower f k`, `lower_from fs k`, `lower_all fs`: lower the functions of a file, with the counter starting at 1.

### Cxx.v: printing C++

- `nl`: newline. `infix_operator s`: `s` is an infix C++ operator.
- `expr_strings e`, `bare_string e`: the printed expression, parenthesized as an operand when infix.
- `stmt_lines ind s`, `block_lines ind l`: the lines of statements.
- `function_name`, `expr_functions`, `stmt_functions`, `called_functions`: the functions a body calls, in order of first use (for the `using std::f;` lines).
- `function_string c`: a template function. `header_string source fs`: the whole header.

### Gallina.v: printing L2′ as Gallina

Assignments become shadowing lets. Loops become `for_up` / `for_down` over
the tuple of the variables they assign. Reals are primitive floats.

- `reserved`, `gname`: the Gallina name of a variable (suffixed `_` when reserved).
- `ty_code`, `code_type`: type codes `R Z B A T` and their Gallina types.
- `env`, `gtype`: the environment of variable types.
- `comparison_op`, `expr_type`, `drop_spaces`, `trim`, `split_slash`, `literal`, `op1_name`, `gallina_op2`, `int_op2`, `expr_string`: expressions.
- `lhs_name`, `add_assigned`, `stmt_assigned`, `assigned`: the variables a block assigns that are defined before it.
- `tuple`, `pattern`, `split_last`, `update_string`, `loop_text`, `branch_text`, `stmt_lines`, `stmts_lines`: statements.
- `param_binder`, `param_result`, `function_text`, `gallina_scoped`, `gallina_function`, `gallina_from`: functions. The `ByRef` parameters are results.
- `preamble`: the Gallina definitions the output relies on (`get`, `set_at`, `add_at`, `pop`, `for_up`, …).
- `gallina_file source fs`.

### Adjudge.v: the driver

- `mode`: `ModeTangent | ModeAdjoint | ModeAdjointValue`. `mode_value m` is `true` for adjoint-value. `mode_name` is its name.
- `check f`: `(Some (normalize f), well_formed …)` when `f` is expressible.
- `differentiate m a`: `tangent`, `adjoint false` or `adjoint true`.
- `transform m a := simplify (differentiate m (annotate (mode_value m) a))`.
- `main m source fs`: the header of the well-formed functions, if any, and the diagnostics `"name: message"` of the refused ones.

### SimplifyCorrect.v: theorem 2, `simplify_correct_tapes`

The proof shows that `simplify` preserves the execution over the reals of a
program that follows `good`, tapes included. It is a simulation between
stores that agree on the variables in scope.

- Local notations: `W`, `out`, `oute`, `outs` (the `out_*` maps at `nat`), `store`.
- `ex ss s`: executes a `W` block over the reals, after `out_dstmt`.
- Ltac `inv_eval`: unfolds an evaluation hypothesis, match by match.
- `gd sc wr ss`: `good` without the `DPush`/`DPop` rules (the tangent programs).
- `after_scope sc ss`, `after_wr wr ss`: the scope and the writable set after a block. `defs ss`, `wdefs ss`: the variables it defines, and those it defines writable.
- `agree sc s s'`: the two stores agree on the variables of `sc` and on `Returned`. This is not the `agree` of TangentCorrect.v.
- `sim sc ss1 ss2`: from stores agreeing on `sc`, every run of `ss1` is matched by a run of `ss2` ending in agreeing stores.
- `lhs_var l`: the variable an assignment target writes.
- `correct f`: the block transformation `f` keeps `gd` and refines every `gd` block.
- `agree_ex v sc s s'`: agreement on `sc` except `v`.
- Section `Replace`: assumes `consistent v` and `real_lit l = Some x`, with local notations `re`/`rs` for replacing `v` by the literal `l`.
- `params ps`: the variables of the parameters.
- Theorems: `simplify_correct_fuel`, and `simplify_correct_tapes` (refinement: same final parameters and returned value).

### Correctness.v: `normalize_correct`, `annotate_correct`

- `term_equiv G t1 t2`, `result_equiv`, `definition_equiv`: two instances of an L0 term are the same term, with the variables of `G : list (V1 * V2)` paired.
- `parametric f`: any two instances of `fdef f` are related with `G = []`.
- `env_ok G`: each pair `(atom, value)` of `G` has the atom evaluating to the value (stage 1).
- Ltac `inv_some`: unfolds `Some`/`None`/match hypotheses.
- `Scheme anf_ind'` (with `value_ind'`): the mutual induction scheme on `anf`/`value`.
- Theorems:
  - `normalize_correct`: when the source computes a value, its A-normal form computes the same, in any domain;
  - `annotate_correct`: the annotated function computes what the function computes.

### AnfEquiv.v: parametricity of L1

- `atom_eq G a1 a2`: related atoms (paired variables, or equal literals).
- `anf_eq G b1 b2` / `value_eq G e1 e2`: two instances of an L1 body or value are the same term. A binder relates its bodies on every pair added to `G`. The annotations are not compared.
- `aresult_eq`, `adefinition_eq`: the same for results and definitions (names, types and roles equal).
- Theorem `normalize_parametric`: the normal form of a parametric source is parametric.

### Euclidean.v: R^n in Coquelicot

- `unit_AbelianMonoid_mixin`, `unit_AbelianGroup_mixin`, `unit_ModuleSpace_mixin`, `unit_UniformSpace_mixin` and the canonical structures `unit_AbelianMonoid`, `unit_AbelianGroup`, `unit_ModuleSpace`, `unit_UniformSpace`, `unit_NormedModuleAux`, `unit_NormedModule`: `unit` as the zero normed module.
- `Rn n`: `R × (R × … × unit)` as a `NormedModule R_AbsRing`.
- `vec_of_list n l`: the first `n` reals of `l`, padded with zeros.
- `list_of_vec n v`: the coordinates of `v`, in order.
- `coord n j v`: the j-th coordinate, a linear map.

### DualsDerive.v: theorem 3, `duals_derive`

Where `f` is `defined` at `x`, it is Fréchet-differentiable (`filterdiff`) as
a function `value_of f x : R^n -> R^m`, and the dual numbers compute its
derivative.

- `digits_value`, `digits_length`, `is_digit_char`: lemmas about reading decimal literals.
- `val_map g v`: maps the numbers of a value by `g`.
- `graph g G`: every pair of `G` is `(x, val_map g x)`.
- Sections `Forward` / `Reflect`: assume that the operations of two domains commute with `g` (forward: success transfers; reflect: the converse).
- Section `EquivInversion`: inversion lemmas on `term_equiv`.
- `real_fun1`, `real_fun2`: the real operations made total (0 on failure).
- `dual_tan1`, `dual_tan2`: the tangent the dual numbers compute.
- `derivative1 f x`: the derivative of a unary operation.
- Section `Families` (around `e0 : E`):
  - a number is a family `fam := (E -> R) * (E -> R)`, a function and its derivative;
  - `good p`: `fst p` is differentiable at `e0` with derivative `snd p`. This is not the `good` of Scoping.v. `good_val` lifts it to values;
  - `fam_lit`, `fam_op1`, `fam_op2`, `fam_cmp`, `families`: the domain of families. It fails where `smooth_reals` fails at `e0`;
  - `at_point y p`: the family at `y`. `dual_at h p`: the family as a dual number at `e0` in direction `h`;
  - Ltac `decide_ifs`: decides the real comparisons in a goal;
  - `ctx_at y G`: relates the family instance to the instance at `y`;
  - `near_ok t1`: for the evaluation of `t1` over families, the value is good, and near `e0` the evaluation over the reals of the instance at `y` gives the value at `y`.
- `reals_of_val`, `reals_of_args`: the real coordinates (reals and array elements) of a value and of a list of arguments.
- `lay_list`, `lay real other x j`: rebuilds the arguments, mapping each real coordinate (numbered from `j`) by `real` and each tape element by `other`.
- `with_reals x r`: `x` with its reals replaced by `r`.
- `in_dim x`: the number of reals of `x`.
- `out_dim f x`: the number of reals of the value of `f` at `x`.
- `value_of f x y`: `f` as a function `Rn (in_dim x) -> Rn (out_dim f x)`.
- `dual_args x dx`: the arguments as dual numbers, each real with the tangent of `dx` at its position.
- `primal_val`, `tangent_reals`: the primal value and the list of tangents of a dual value.
- `val_reals`: `reals_of_val` in any domain.
- `famn n`, `fam_lay`, `fam_args x`: the arguments as families on `R^n`. The j-th real coordinate is the j-th coordinate function, and a tape element is a constant.
- `point_of x`: the vector of the reals of `x`.

### TangentCorrect.v: theorem 1, the simulation (lets, operations, branches)

The proof shows that the tangent program, run over the reals, computes the
dual evaluation (see Key concepts).

- `keyv`, `xev`, `run`: the store key of a `W` variable, and evaluation and execution after `out_*`.
- `dfst`, `dsnd`: the parts of a dual number.
- `primal v`, `tangent v`: the primal and tangent parts of a dual value, as values of the reals. This `tangent` is not `Tangent.tangent`.
- `zero v`: the tangent of `v` is zero.
- `has_type t v`: `v` is a value of type `t`, an array having the declared extent.
- `real_or_array t`, `is_array t`: predicates on types.
- `pv` (record): `pa`, `pw`, `pt`, `pd`, `pn` (see Key concepts). `stored p := DBound (pn p, pn p)`.
- `gA`, `gW`, `gT`, `gD`: the contexts pairing each `pv` with its projection.
- `amap f a`: maps the variable of an atom.
- `static_ok k p`: see Key concepts.
- `ids_unique L`: two variables of `L` with the same `vid` are equal.
- `store_ok s p`: the store holds the primal value in `stored p`, and the tangent in its dot when it has one.
- `pplace`, `wplace`, `owner`, `inplace`, `place_ok`: see Key concepts.
- `store_full s p`: the store holds both the value and the tangent, even when `p` is not varied.
- `arrays_len s n len`: `n` and `DotOf n` hold arrays of length `len`.
- `ctx_ok L k c s wP pp live ty` (record), the invariant of a body:
  - `c_static`: `static_ok k` on `L`;
  - `c_unique`: `ids_unique`;
  - `c_num`: storages below `c`;
  - `c_store`: live variables are `store_ok`;
  - `c_written`: the written atom is an argument in scope;
  - `c_place`: `place_ok`;
  - `c_owner`: a variable sharing the owner's storage is the owner, or is not live;
  - `c_inplace`: such a live variable is `store_full`;
  - `c_arrays`: a live array that is not an argument (or is the written one) lives in the owner's storage;
  - `c_ty`: an array body has an owner;
  - `c_top`: at the top with a written array, the body has its type, it is varied when live, and its storage and dot have the declared length.
- `sctx L k c wP pp live ty` (record): the store-independent fields (`s_static`, `s_unique`, `s_num`, `s_written`, `s_place`, `s_owner`, `s_arrays`, `s_ty`, `s_top`).
- `below c v`, `frame c ex s s'`: see Key concepts.
- `body_result t ex s ve de v`: for a real, `ve`/`de` give the primal/tangent of `v`. For an array, the storage `ex` and its dot hold them.
- Ltac `unfold_ops H`: unfolds the domain operations, but not the reading of literals.
- `pfresh k`: a `pv` opened with identity `k` (probe, `VInt 0`, number 0).
- `agree G1 G2 k`: two `vinfo` contexts give the same identity to a `pv`, below `k`. This is not the `agree` of SimplifyCorrect.v.
- Ltac `rewrite_atoms`: rewrites `occurs_atom` across related contexts.
- `dvars e`: the variables an expression reads.
- `res_vars L live c e`: `e` reads only stored variables or dots of live variables in scope, or variables opened at or after `c`.
- `dot_vars L live c e`: the same, with only the dots of variables in scope.
- `live_anf k b p`, `live_value k e p`: `p` occurs in the body or value.
- `sim_body bP`, `sim_value eP`, `storage`: see Key concepts.
- `avoid k e`: no variable of `e` has the key `k`.
- Ltacs `graph`, `fresh_case`, `crush_match`, `value_intro`: proof automation (inverting the four `value_eq`, destructing matches).

### TangentLoops.v: theorem 1, the loops

There are no new definitions. The file proves the cases of the map, the
scalar fold and the in-place fold, and then `simulation`:
`(forall bP, sim_body bP) /\ (forall eP, sim_value eP)`.

### TangentGood.v: theorem 1, the scoping discipline (`scoping`)

- `good_k sc wr c' ss Q`: `ss` followed by any block that is `good` in every larger scope opened before `c'` where `Q` holds, is `good` from `(sc, wr)`.
- `scope_ok L c wP pp live sc wr`: `sc` holds consistent variables opened before `c`, including the storage (and dot) of every live variable. The owner's storage and dot are writable.
- `good_body bP`, `good_value eP`: the analogues of `sim_body`/`sim_value` without store. The generated code keeps the discipline (`good_k`), its result expressions being in scope.
- `allv P e`: `P` holds of every variable of `e`.
- Ltac `gvalue_intro`: the introduction pattern of `good_value`.
- `default_dual t`: a value of type `t` with zero tangents.

### TangentTop.v: theorem 1 for a function (`tangent_simulates_duals`)

- `arg_pv n t r k x`: the `pv` of the k-th argument: identity `k`, stored in the k-th parameter, dual value `x`.
- `open_P d k xs L`: opens the arguments of the `pv` instance with `arg_pv`, accumulating them last first. It returns the arguments, the result and the body.
- `arg_entry p`: the `(decl, stored variable)` that the tangent pass records for an argument.
- `decls f`: the declarations of the arguments of `f`.
- `has_dot d`: the argument has a tangent parameter (not integer, not passive).
- `fits d v`: the argument value fits its declaration (an array has its extent).
- `nreals v`: 1 for a real, the length of an array, 0 otherwise.
- `seed ds x dx`: the tangents, `dx` on the reals of independent and inout arguments and 0 elsewhere.
- `pair_with l t`, `val_dual v t`, `seed_args ds x dx`: the arguments as dual numbers with the seeded tangents.
- `tangent_inputs ds x dx`: the arguments of the tangent function: the primal values, then the tangent of each argument with a dot, then 0 for the tangent of a returned real.
- `dot_out d`: the tangent parameter of the argument is an output only (a written dependent argument).
- `tangent_inputs_with dd r0 ds x dx`: as `tangent_inputs`, with any initial values in the output-only tangent parameters: `dd v` for a written dependent argument of primal `v`, `r0` for the tangent of a returned real. `zero_dot v`: the zero tangent of `v`; `tangent_inputs_zero`: `tangent_inputs` is the instance `tangent_inputs_with zero_dot (VReal 0)`.
- `open_args_facts`: the facts on the arguments `open_P` opens (positions, distinct numbers, `static_ok`), shared with `adjoint_simulates_duals`.
- `tangent_simulates_duals_with`: theorem 1 for any initial values in the output-only tangent parameters (fitting their declaration); `tangent_simulates_duals`, its instance with zeros.
- `index_of_written ds i`: the position of the written argument.
- `tangent_output ds out`: the value and tangent the tangent function gives: the returned value and the last parameter, or the written argument and its tangent parameter.
- `prim_entries AL`, `dot_val dd p`, `dot_in dd p`, `dot_entries dd AL`: the initial store of the tangent function.

### TangentMode.v: `tangent_mode_correct`

Notations re-export `fits`, `decls`, `seed`, `tangent_inputs`,
`tangent_output` from TangentTop.v. The theorem combines `duals_derive`,
`normalize_correct`, `tangent_simulates_duals_with` and `simplify_correct_tapes`. For a
parametric, well-formed `f` defined at `x`:
- `f` has a value `v` and a derivative `df`;
- the simplified tangent program on `tangent_inputs (decls f) x dx` returns
  `v` and a tangent `w` whose reals are `df (seed … dx)`.

`tangent_mode_correct_with dd r0` is the same on `tangent_inputs_with dd r0
(decls f) x dx`, for any initial values of the output-only tangent parameters
(`dd v` fitting the declaration of a written dependent argument of primal
`v`); `tangent_mode_correct` is its instance with zeros.

### AdjointSpec.v: the layout of the adjoint function

- Notations `has_dot`, `nreals` (from TangentTop.v).
- `with_list v l`: `v` with its reals replaced by those of `l`.
- `bar_inputs ds x xb yb`: the adjoints given to the function: the seed `yb` for the written argument, the slices of `xb` for the others with a dot.
- `adjoint_inputs ds x xb yb`: `x`, then `bar_inputs`, then the seed of a returned real.
- `lsub a b`: elementwise difference.
- `gradient ds x xb bars`: for each argument with an adjoint, its final minus its initial adjoint (the final value for the written argument); 0 for the others.
- `value_given ds out`: the value adjoint-value gives back: the returned value, or the final value of a dependent written argument.
- `writes_inout ds`: some argument is inout.
- `adjoint_output ds x xb out`: the gradient computed from the final values of the adjoint parameters.
- `dotl a b`: the dot product of two lists of reals.

### AdjointCorrect.v: the adjoint simulation (operations, pairing, lets)

This file is being edited (milestone M5b). The definitions are described as
they are now. See Key concepts for pairing, owners, contexts, frames,
`asim_*`, and fold traces and tapes.

- `pmentions p`: the partial derivative is not a constant, so it may read its operand.
- `coef_a f x y`, `coef_b f x y`: the partial derivatives of the binary arithmetic operations at `(x, y)`.
- `barv`, `dotr`, `inner`, `shaped`, `owners`, `pairing`, `oset`, `oput`: the pairing.
- `owners_ok O`: the storages of `O` are consistent.
- `useful cv m k b p`, `tbr cv m k b p`: `p` is in the U and in the L of `needs`.
- `not_in_loop pp`.
- `actx` (record): fields `a_sctx`, `a_bar`, `a_store`, `a_tape`, `a_owner`, `a_tid`.
- `is_tape`, `is_bar`, `is_primal`: the kind of a store key. A primal key is `DBound _` or `ResultVar`.
- `vo_target vo`: where adjoint-value leaves the value.
- `fwd_frame`, `tapes_kept`, `tapes_same`, `tkeep`, `rev_frame`, `rev_frame_x`, `agree_prim`: the frames.
- `rctx` (record): fields `r_nodup`, `r_shape`, `r_below`, `r_useful`, `r_value`, `r_owner`, `r_args`, `r_written`.
- `seed_ok`, `seed_value`, `result_pairing`, `vo_result`, `vo_kept`.
- `bar_target l`, `bar_stmt st`: an assignment, accumulation or definition whose target is an adjoint. Such code leaves the other keys unchanged.
- `fold_trace`, `real_of` (the primal real of a dual value, 0 otherwise), `set_index`, `body_pushes`, `fold_pushes`, `tail_fold_live`, `fold_live`.
- In section `Sim` (variable `cv`):
  - `same_ex`, `tapes_ok`, `fold_tape`, `ptail`, `tail_tape`;
  - `asim_body`, `asim_fwd`, `asim_rev0`, `asim_rev`;
  - `vreads k e p`, `vflows k e p`, `vatoms k e p`: `p` is among the reads of the reverse sweep of `e`, the atoms its adjoint flows to, and the atoms of `e`;
  - `inplace_only eP`: a value stored in place outside a loop (a map) writes an argument that it does not read. A varied owner makes the value varied, and an owner that is not live is not varied;
  - `act_value eP`: the activity analysis is sound for a value. It has its type, a zero tangent when not varied, and is a real or array when varied;
  - `act_owner eP`: a value updated in place that is not varied leaves the tangent of its owner unchanged (`tangent (pd o) = tangent ve`);
  - `straight_value e`, `straight b`: bodies whose lets bind only operations, reads and sets (no branch, no loop);
  - Section `NeedsLet`: `Let x := let_binder k eA`, with local tactics `needs_let_tac`, `split_reads`, `below_tac` for the lemmas on `needs` at a let;
  - Ltacs `none_case`, `fwd_intro`, `rev_intro`, `act_intro`, `fresh_case'`: proof automation.
- `dvar_eq_dec_c` is a lemma: decidable equality of `dvar W`.
- `ptype eP`: the type of a value read through the types of its atoms (`WellFormed.type_of` on the `pv` instance); `ptype_ok`: a well-typed value has it. `asim_let_typed` (and `act_let_typed`, `psim_let_typed` in AdjointBranch.v): the let, its continuation simulated only for the binders of that type; `asim_let`, `act_let`, `psim_let` are their instances. The class `nesty` (AdjointNesty.v) quantifies its lets over those binders only: a fold on a computed init is then scalar.

### AdjointBranch.v: branches, maps and scalar folds (milestone M2)

- `dummy_tvar`: a placeholder `tvar`. `opened k`: a `pv` opened by both analyses at `k`.
- `act_body bP`: the value of a body has its checked type, and a zero tangent when the body is not varied.
- `odel O n`: the owners without the storage `n`.
- Section `Branch` (variable `cv`):
  - `tape_step r zi st t`: when `r`, the tape `t` with the element of `st` at index `zi` pushed;
  - `same_except zi l0 l1`: two arrays of the same length that differ at most at index `zi`;
  - `psim_body bP`: see Key concepts;
  - `ibody st b`: the body of an in-place loop on the state `st`: operations and reads, then a set or an in-place fold on `st` that is the tail, or `st` itself;
  - `abody b`: the body of an in-place loop: operations and reads, then a set that is the tail;
  - `branchy top b` / `branchy_value top e`: the shape the file's theorem covers. Sets, maps and folds appear only at the top (`top = true`). Branches, maps and folds contain none of them. A fold is scalar;
  - Ltacs `fwd_intro`, `rev_intro`.
- The simulation of `branchy` bodies follows from that of the larger classes: `straight_branchy`, `branchy_foldy` (`AdjointFoldy.v`) and `foldy_nesty` (`AdjointTop.v`) include each class in the next, and `adjoint_straight_duals`, `adjoint_branchy_duals`, `adjoint_foldy_duals` are corollaries of `adjoint_nesty_duals`.

### AdjointFold.v: folds updating an array in place (milestone M5)

It has no definitions, only lemmas in ssreflect style, in section `Fold`
(variable `cv`):
- on `abody` bodies: `tail_index_abody`, `adj_replay_abody`, `adj_rev_bars_abody`, `abody_eval_array`;
- on owners: `oset_oset`, `oset_in`, `oset_other`, `oset_mem`;
- `fold_pushes_snoc`, `run_pop_at`;
- `afwd_fold_body` (`asim_fwd` for an in-place fold, for any class of steps).
The two sweeps of an in-place fold are `afwd_fold_nbody` and `arev_fold_nbody`
(AdjointNBody.v).

### AdjointNBody.v: in-place loops of any depth (milestone M5b)

In section `NBody` (variable `cv`):
- `nbody s b`: the body of an in-place loop on the state `s`: operations and
  reads, then a set that is the tail, or an in-place fold on `s` that is the
  tail and whose steps are again `nbody` on their own state, or `s` itself.
  `nbody_ind` is its induction principle, through the inner folds.
- `aset_tail k bA`: the analysed body ends with a set. With
  `tail_fold_live` (it ends with a fold), it tells the three kinds of steps
  apart: `nbody_abody`, `nbody_ret_needs`.
- The state of a loop whose step ends with a fold, or gives the state back,
  is not read by the reverse loop (`nbody_needs`, `nbody_state_dead`,
  `nbody_ret_dead`), so a recorded state means a step ending with a set
  (`nbody_live_set`).
- `nbody_records`, `records_fold_nbody`: a loop records iff it is live
  (`fold_live`); `nbody_tail_state`, `tail_state_nbody`: a step ending with
  an inner fold has that liveness as its `tail_fold_state`.
- The pieces of the simulation of a step: `nbody_ibody`, `nbody_act`,
  `nbody_psim` (with `psim_fold_nbody`), `adj_replay_nbody`,
  `adj_rev_bars_nbody`, `tail_tape_nbody`.
- `afwd_fold_nbody`, `arev_fold_nbody`: the two sweeps of an in-place fold
  whose steps are nbodies. The reverse loop pops the element a step ending
  with a set overwrote when the state is recorded, gets the state back from
  the inner fold of a step ending with one (`tail_back`), and leaves it
  otherwise.
- `nbody_asim`: the adjoint simulation of an nbody, by induction on the
  depth.

### AdjointTop.v: the adjoint simulation for a function

- `keeps s s'`: every key present in `s` is present in `s'`. `exec_keeps` is a recursive proof that `exec` keeps keys.
- `param_store ps args`: the store `exec_scoped` builds from parameters and arguments. `pvar p`: the variable of a parameter.
- `decl_role d`, `decl_ty d`: the role and type of a declaration.
- `slice d v dx`: the slice of `dx` for the argument `v`, or zeros when its role is not varied.
- `grad_rhs ds x xb dx bars`: Σ over arguments with an adjoint of (tangent · final adjoint − tangent · initial adjoint), the initial term omitted for the written argument.
- `bars_fit ds x bars`: the final adjoints have the sizes of their arguments.
- `dname p`: the declaration of an argument `pv`.
- `owners_of Ls`: the arguments with a dot, as owners (tangent, storage).
- `init_sum Ls s`: Σ tangent · adjoint in `s` over the non-written arguments with a dot.
- `written_sum Ls s`: the same term for the written argument.
- `bars_in Ls s bars`: the adjoints of the arguments in `s` are `bars`, in order, and shaped.
- `bars_list Ls s`: the final adjoints of the arguments, in order.
- `final_of s q`: the final value of a parameter (`VInt 0` when absent).
- `ty_size t`: 1 for a real, the extent of an array, 0 otherwise.
- Theorem `adjoint_simulates_duals`: the adjoint function, opened at the numbers `simplify` uses and run on the primal arguments, their adjoints and the seed, computes the gradient, the transpose of the tangent of the dual evaluation applied to the seed.

### AdjointMode.v: `adjoint_mode_correct`

Notations re-export `fits`, `decls`, `seed`. For a parametric, well-formed `f`
defined at `x`, with value `v` and derivative `df`:
- the simplified adjoint program on `adjoint_inputs (decls f) x xb yb`
  produces a gradient `g`;
- for every `dx`, `<df (seed dx), yb> = <seed dx, g>` (`dotl`);
- in adjoint-value without an inout argument, `value_given` is `v`.

### AdjointGood.v, AdjointGoodFwd.v, AdjointGoodRev.v: the scoping of the adjoint code (milestone M6)

- `fscope L c wP pp rd sc wr`: the scope `sc` (and its writable part `wr`) holds the storage of every variable the code reads (`rd`), and the owner is writable.
- `tape_fwd`, `tape_rev`: the tape of the owner is declared before its pushes and pops (at the top by the in-place fold itself, in a loop body by the enclosing loop).
- `bars_ok`: the adjoint (bar) of every useful variable, and of the owner, is declared before it is incremented.
- `fold_slive k e`: the `state_live` of a fold value, false otherwise.
- `agood_prim`, `agood_value`: the forward code (`prim`, `fwd_value`) follows `good` from such a scope. `agood_body`, `agood_rev`: so does the code of `adj` and `rev_value`, its reverse part from any extension of the scope the forward part leaves (`rscope`), with no variable the reverse defines clashing with the forward ones (the numbers `F` of the forward part).
- Theorems `agood_fwd` (AdjointGoodFwd.v) and `agood_adj` (AdjointGoodRev.v): for every body and value, by induction, with no body class.

### AdjointExamples.v: the class premise is not vacuous

- `nesty_args f`: the class premise of `adjoint_nesty_duals` for `f`, for every `x`, `dx`.
- For nine programs (straight line, branch, map, scalar fold, in-place loop, nests of depth 2 and 3, steps returning their state), `<name>_wf` (well-formed, by `vm_compute`) and `<name>_nesty`.
- `computed_init_nesty`: a fold whose initial value is computed by a let (the let binds a real, the type of its value).

### AdjointClassify.v: every well-formed function is in `nesty`

- `fpv k t`: a binder opened at identity `k`, of type `t`, not varied.
- `hinv H L`, `htyped H`: `H` relates each variable of `L` to one variable of the target instance, of the same type.
- `tc_op1` … `tc_fold`, `tc_nontail`: what `typecheck` says of each value.
- `hret`: the arrays a step may not return (not read by the step, or arguments other than the written one).
- `nbody_wf`, `nesty_false_wf`, `nesty_top_wf`: from `typecheck` on the `vinfo` instance, through a `pv` instance opened at fresh binders, the class of the target instance.
- Theorem `well_formed_nesty`: a parametric, well-formed function has its opened body in `nesty`.

### AdjointWf.v

- Corollary `adjoint_wf_duals`: `adjoint_nesty_duals` without the class premise.

### AdjointModeProof.v: `adjoint_mode_correct` from the simplified corollary

- Section hypothesis `adjoint_simplified`: the simplified adjoint function computes the gradient (the conclusion of `adjoint_nesty_duals`, without the class premise, on `exec_dfunction reals (simplify ...)`).
- `adjoint_mode_correct_from`: the statement of `adjoint_mode_correct` from it, with `eval_smooth_reals` and `out_dim_value`.
