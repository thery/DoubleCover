# Reading the elpiDiff Rocq development: a tutorial

This tutorial is for readers who know the basics of Rocq and the idea of
automatic differentiation (tangent mode, adjoint mode, tapes), but who have
never opened this development. When you reach the end, you should be able to
open any `.v` file of this directory, read a lemma, and tell what it says
and why it is there.

We go from the big picture down to the details, and we follow one tiny
function all the way. Two companion documents are the reference: the
glossary [DEFINITIONS.md](DEFINITIONS.md) and the overview
[README.md](README.md). This tutorial explains how the pieces fit, and it
links to the glossary rather than repeating it.

Contents:

1. What is proved, in one page
2. The languages and their Rocq types
3. How the proofs relate two programs
4. The tangent proof, the simpler model
5. The adjoint proof
6. Reading one real lemma end to end
7. Reading the proof scripts
8. A map of the files, in reading order
9. Pointers

---

## 1. What is proved, in one page

### The tool

elpiDiff is a source-to-source automatic differentiation tool written in
Elpi. It reads a small functional language, and it writes C++ functions that
compute the derivative: a tangent function (forward mode) and an adjoint
function (reverse mode). This directory mirrors the tool in Rocq, one
function per Elpi predicate, and proves the passes correct. The Rocq passes
really compute: `Compute (main ModeAdjoint "f.elpi" [f])` gives the C++
header that the Elpi tool writes. The script `rocqtest.py` checks that the
two agree character for character on the reference cases
(see [tools/README.md](../tools/README.md)).

The pipeline is a chain of passes between languages:

```
L0 source --normalize--> L1 (A-normal form) --annotate--> L1ᵃ (annotated)
   --tangent / adjoint--> L2 (imperative IR) --simplify--> L2′ --lower--> L3 (C++)
```

- `normalize` (Normalize.v) names every intermediate value with a `let`.
- `annotate` (Annotate.v) runs the analyses (activity, to-be-recorded) and
  stores their verdicts on each `let` and each fold.
- `tangent` (Tangent.v) and `adjoint` (Adjoint.v) generate derivative code
  in L2, a small imperative language with loops, arrays and tapes.
- `simplify` (Simplify.v) propagates copies and constants and removes dead
  definitions.
- `lower` (Lower.v) and the printers (Cxx.v) produce C++. These last passes
  are not proved: the proofs stop at L2′, executed by the evaluator `exec`
  of Exec.v.

### A running example

We follow this function through the whole tutorial:

```
T f(T x, T y) { return x * y + sin(x); }
```

In the tool's input syntax (an Elpi term, the C++ is only a comment), it is:

```
primal (function "f" (arg "x" real independent x\ arg "y" real independent y\ body (returns real)
  (op2 add (op2 mul x y) (op1 sin x)))).
```

and the script `tools/torocq.elpi` prints it as a Rocq term of L0:

```
Definition f_fn : function := Function_ "f" (fun V => Arg "x" Real Independent (fun x1 => Arg "y" Real Independent (fun x2 => Body (Returns Real) (Op2 Add (Op2 Mul (Var x1) (Var x2)) (Op1 Sin (Var x1)))))).
```

After `normalize`, every intermediate value has a name. This is the output
of the tool's `dump -- anf`:

```
f(x: real independent, y: real independent) returns real:
    let t1 = x * y
    let t2 = sin(x)
    let t3 = t1 + t2
    return t3
```

`annotate` adds the verdicts of the analyses (`dump -- annotated adjoint`).
All three lets depend on an independent argument (*varied*) and the result
depends on them (*useful*), so all three are *active*:

```
f(x: real independent, y: real independent) returns real:
    let t1 = x * y    [varied, active]
    let t2 = sin(x)    [varied, active]
    let t3 = t1 + t2    [varied, active]
    return t3
```

The tangent code in L2 (`dump -- derivative tangent`) computes each value
and its tangent (`_dot`) side by side:

```
f_tangent(x: real, y: real, x_dot: real, y_dot: real, result_dot: ref real) returns real:
    const real t1 = x * y
    const real t1_dot = (y * x_dot) + (x * y_dot)
    const real t2 = sin(x)
    const real t2_dot = cos(x) * x_dot
    const real t3 = t1 + t2
    const real t3_dot = t1_dot + t2_dot
    result_dot := t3_dot
    return t3
```

The adjoint code (`dump -- derivative adjoint`) has a forward sweep and a
reverse sweep. Here the forward sweep is *empty*. The reverse sweep only
reads `x` and `y` (the partial derivatives of `x * y` are `y` and `x`, and
the one of `sin x` is `cos x`). It never reads `t1`, `t2` or `t3`, so the
to-be-recorded analysis decided that nothing has to be computed forward:

```
f_adjoint(x: real, y: real, x_bar: ref real, y_bar: ref real, result_bar: real):
    var real t1_bar = 0
    var real t2_bar = 0
    var real t3_bar = 0
    t3_bar += result_bar
    t1_bar += t3_bar
    t2_bar += t3_bar
    x_bar += cos(x) * t2_bar
    x_bar += y * t1_bar
    y_bar += x * t1_bar
```

After `simplify` (`dump -- simplified adjoint`), each mutable adjoint that is
written only once becomes a constant:

```
f_adjoint(x: real, y: real, x_bar: ref real, y_bar: ref real, result_bar: real):
    const real t3_bar = result_bar
    const real t1_bar = t3_bar
    const real t2_bar = t3_bar
    x_bar += cos(x) * t2_bar
    x_bar += y * t1_bar
    y_bar += x * t1_bar
```

Section 5 shows an example with a loop and a tape.

### The two end theorems

The goal is two theorems, one per mode. Here they are, copied from the
files.

`tangent_mode_correct` (TangentMode.v) is proved:

```
Theorem tangent_mode_correct (f : function) (x : list (val R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x -> defined f x ->
  exists v df,
    eval_function smooth_reals f x = Some v /\
    filterdiff (value_of f x) (locally (point_of x)) df /\
    forall dx, length dx = in_dim x ->
      exists out w,
        exec_dfunction reals (simplify (tangent (annotate false (normalize f))))
          (tangent_inputs (decls f) x dx) = Some out /\
        tangent_output (decls f) out = Some (v, w) /\
        reals_of_val w = list_of_vec _ (df (vec_of_list _ (seed (decls f) x dx))).
```

In words: take a source function `f` and arguments `x`, and assume:
- `parametric f`: the source is a genuine PHOAS term (section 2);
- `well_formed (normalize f) = Ok`: the tool accepts `f`;
- `Forall2 fits (decls f) x`: the arguments fit the declared types;
- `defined f x`: the evaluation is defined at `x` in the sense of Abadi and
  Plotkin, that is, it never compares two equal reals (Smooth.v).

Then `f` evaluates to some `v`, it is differentiable at `x` with a
derivative `df` (Coquelicot's `filterdiff`), and for any tangent direction
`dx` the generated and simplified tangent function, run over the reals,
returns `v` and `df` applied to the seed of `dx`.

`tangent_inputs` passes 0 in the tangent parameters that are outputs only
(`result_dot`, the tangent of a written dependent argument). The general
version, `tangent_mode_correct_with dd r0`, gives the same conclusion on
`tangent_inputs_with dd r0 (decls f) x dx`, for any initial values there:
the generated code never reads them.

`adjoint_mode_correct` (AdjointMode.v) is only **stated**. It is the one
`Admitted` of the development:

```
Theorem adjoint_mode_correct (cv : bool) (f : function) (x : list (val R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x -> defined f x ->
  exists v df,
    eval_function smooth_reals f x = Some v /\
    filterdiff (value_of f x) (locally (point_of x)) df /\
    forall xb yb, length xb = in_dim x -> length yb = out_dim f x ->
      exists out g,
        exec_dfunction reals (simplify (adjoint cv (annotate cv (normalize f))))
          (adjoint_inputs (decls f) x xb yb) = Some out /\
        adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
        (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some v) /\
        forall dx, length dx = in_dim x ->
          dotl (list_of_vec _ (df (vec_of_list _ (seed (decls f) x dx)))) yb = dotl (seed (decls f) x dx) g.
Proof.
Admitted.
```

The last line is the dot-product test, the defining property of an adjoint:
for every direction `dx`, ⟨df · dx, yb⟩ = ⟨dx, g⟩, where `g` is the gradient
the adjoint function returns for the output weights `yb`. The flag `cv`
selects the mode *adjoint-value*, which also gives back the value of `f`.

### Where the proof stands

The adjoint proof is built in milestones (README.md has the table):
- **M1 to M5 are done.** They cover straight-line code, branches, maps,
  scalar folds, folds that update an array in place, and nests of two such
  folds. The results are the top-level corollaries `adjoint_straight_duals`,
  `adjoint_branchy_duals`, `adjoint_foldy_duals` and `adjoint_nesty_duals`
  (AdjointTop.v). They relate the adjoint code *before* `simplify` to the
  dual-number evaluation of the source.
- **M6 is partial.** `simplify_correct_tapes` (SimplifyCorrect.v) proves
  that `simplify` is correct on code with tapes, under a scoping discipline
  called `good`. The proof that the adjoint code is `good` remains to be
  done.
- **M7 is open.** It will assemble everything into `adjoint_mode_correct`.
  It also needs every well-formed program to fall into one of the classes of
  bodies the proofs handle (section 5.6).

### What you have to trust

Besides Rocq itself, you trust the statements, and the axioms that
`Print Assumptions tangent_mode_correct` lists: the axioms of the reals of
the standard library (`sig_forall_dec`, `sig_not_dec`,
`functional_extensionality_dep`, `classic`), which Coquelicot uses as well.
You also trust that the Rocq passes are the Elpi ones; `rocqtest.py` checks
this on the reference cases, but it is a test, not a proof.

---

## 2. The languages and their Rocq types

### PHOAS in five minutes

The tool is written in Elpi, where binders are λ-terms (`let E (x\ B)`). In
Rocq, the development uses PHOAS, *parametric higher-order abstract syntax*.
A type of terms takes the type `V` of its variables as a parameter, and a
binder is a Rocq function. Here is L0 (Syntax.v):

```
Inductive term : Type :=
| Var (x : V)                                     (* a bound variable *)
| Num (s : string)                                (* a real literal, spelled as in C++: "2", "0.9" *)
| Nat (k : Z)                                     (* an integer literal *)
| Op1 (f : unary) (a : term)                      (* a unary elementary operation *)
| Op2 (f : binary) (a b : term)                   (* a binary elementary operation *)
| Get (a i : term)                                (* a[i] *)
| Set_ (a i v : term)                              (* a with a[i] replaced: the next version of a *)
| Let_ (e : term) (b : V -> term)                  (* let x = e in b *)
| Ite (c t e : term)                              (* if c then t else e, where c is passive *)
| Map (lo hi : term) (b : V -> term)              (* the array [ b i | lo <= i < hi ] *)
| Fold (lo hi init : term) (b : V -> V -> term).  (* s := init; for lo <= i < hi: s := b i s *)
```

`Let_ e b` binds a variable in `b : V -> term`. There is no string name and
no de Bruijn index. A closed program does not choose `V`: it is a function
`forall V, ...`. Look at `f_fn` above: `Function_ "f" (fun V => ...)`.

Why go to that trouble? Because each pass, and each proof, picks the `V` it
needs and *instantiates* the same program at it. To open a binder `b`, you
apply it to a variable of your chosen type:
- the evaluators take `V := val N` (values) and compute `eval (b v)`;
- `normalize` takes `V := atom V'`, so a source variable *is* its atom in
  the output;
- `well_formed` takes `V := vinfo`, a record with an identity, a type and
  an argument role;
- the analyses take `V := avar`, an identity with a varied flag;
- `tangent` and `adjoint` take `V := tvar V'`, a record of everything they
  know of a variable (where it is stored, whether it has a tangent, an
  adjoint, a tape, ...);
- the L2 evaluator takes `nat`, and the proofs of L2 take `W := nat * nat`.

`annotate` (Annotate.v) shows the idea in two lines. It instantiates its
input twice: once at `avar` to compute the annotations into a tree `t`, and
once at the output's `V` to rebuild the term with them:

```
Definition annotate (cv : bool) (f : afunction bare) : afunction ann :=
  let t := annotate_definition_t (annotate_cv cv f) 0 (afdef f avar) in
  AFunction (afname f) (fun V => rebuild_definition V (afdef f V) t).
```

To look *inside* a binder, an analysis must invent a variable. It numbers
them: it applies the binder to a variable with identity `k` and continues at
`S k`. This is why most analyses take an argument `k`, and why you will see
`anon k`, `fresh k`, `let_binder k e` and `opened k` everywhere. These are
the variables numbered `k` at the types `vinfo`, `avar`, and so on.

### L1: A-normal form (Anf.v)

L1 is L0 where every operand is an *atom* (a variable or a literal), and
every intermediate value is bound by a `let`:

```
Inductive atom : Type :=
| AVar (x : V)                                    (* a variable bound by L1 *)
| ANum (s : string)                               (* a real literal *)
| ANat (k : Z).                                   (* an integer literal *)

Variable I : Type.                                (* the annotations: bare or ann *)

Inductive value : Type :=                         (* what a let binds *)
| AOp1 (f : unary) (a : atom)
| AOp2 (f : binary) (a b : atom)
| AGet (a i : atom)                               (* a[i] *)
| ASet (a i v : atom)                             (* a with a[i] replaced *)
| AIte (c : atom) (t e : anf)                     (* the condition is an atom, the branches are bodies *)
| AMap (lo hi : atom) (b : V -> anf)
| AFold (ann : I) (lo hi init : atom) (b : V -> V -> anf)
with anf : Type :=                                (* a body *)
| ALet (ann : I) (e : value) (b : V -> anf)
| ARet (x : atom).
```

The second parameter `I` is the type of annotations. `anf V bare` is plain
L1. `anf V ann` is L1ᵃ, where each let carries `LetAnn varied active
computed`, and each fold carries `FoldAnn varied recorded records`. Our
example is, in Rocq notation:
`ALet _ (AOp2 Mul (AVar x) (AVar y)) (fun t1 => ALet _ (AOp1 Sin (AVar x)) (fun t2 => ...))`.

### L2: the derivative IR (Derivative.v)

L2 is imperative. A variable of the generated code is a `dvar`. Its
derived variables (tangent, adjoint, tape) are built from it by
constructors, never by renaming:

```
Inductive dvar : Type :=                          (* a variable of the generated code *)
| DBound (x : V)                                  (* bound by Named or Fresh *)
| DotOf (v : dvar)                                (* its tangent *)
| BarOf (v : dvar)                                (* its adjoint *)
| TapeOf (v : dvar)                               (* the tape of its successive values *)
| ResultVar.                                      (* the returned value: its tangent or adjoint is an argument *)
```

So `t1_bar` in the dump is `BarOf t1`, and `t1_tape` is `TapeOf t1`. The
statements (`dstmt`) are what you expect: `DDefine`, `DAssign`,
`DIncrement` (the `+=` of adjoints), `DBranch`, `DFor`, `DForBack` (a loop
running downward), and `DTape`, `DPush`, `DPop` for tapes. Generated code is
wrapped in `scoped`, which binds each fresh local:

```
Inductive scoped (A : Type) : Type :=
| Named (n : string) (f : V -> scoped A)          (* an argument, with its C++ name *)
| Fresh (p : string) (f : V -> scoped A)          (* a local, with the prefix of its name *)
| Done (a : A).
```

### The evaluators: the semantics

Each language has an evaluator that returns an `option`, `None` when the
program goes wrong:
- `eval_function` (Eval.v) runs L0;
- `aeval_function` (EvalAnf.v) runs L1 and L1ᵃ;
- `exec_dfunction` (Exec.v) runs L2 over a `store`, a list of
  `(key, val N)` pairs.

The evaluators of L0 and L1 are parametric in a `domain` of numbers
(Domain.v): a record with literals, operations and comparisons. Three
domains matter:
- `reals`: the reals of Rocq;
- `duals`: dual numbers over a domain. A value is a pair (primal value,
  tangent), and evaluating with duals *is* forward-mode differentiation;
- `smooth_reals` (Smooth.v): the reals, but a comparison of two equal reals
  is undefined. This is the partial semantics of Abadi and Plotkin, and
  `defined f x` is defined with it.

The values are `val N`: `VReal`, `VInt`, `VBool`, `VArray`, plus `VTape`,
which only L2 uses.

### The `pv` record: all instances at once

The proofs need to talk about one variable as *every* pass sees it. They
instantiate the L1 program once more, at the record `pv` (TangentCorrect.v):

```
Record pv : Type := PV { pa : avar; pw : vinfo; pt : tvar W; pd : val (dual R); pn : nat }.

Definition stored (p : pv) : dvar W := DBound (pn p, pn p).
```

A `pv` bundles:
- `pa`: what the analyses know (identity, varied);
- `pw`: what `well_formed` knows (identity, type, role);
- `pt`: what the transformations know;
- `pd`: the value in the dual-number evaluation, that is, the primal value
  and the tangent in direction `dx`;
- `pn`: the number of the generated variable that stores it.

The body at `pv`, called `bP` in the statements, is the "master copy". The
four other instances (`bA`, `bW`, `bT`, `bD`) are its projections. The next
section shows how the proofs say so.

---

## 3. How the proofs relate two programs

### The problem

Nothing in Rocq forces `afdef f avar` and `afdef f (val (dual R))` to be the
same term. A function `fun V => ...` could inspect `V` and do different
things. So a proof that reasons about the analysis (at `avar`) and the
evaluation (at `val (dual R)`) of the same body must *assume* that the two
are instances of one term. `parametric f` is that assumption for the source,
and `normalize_parametric` (AnfEquiv.v) transfers it to L1.

### `anf_eq`: two instances are the same term

AnfEquiv.v defines the relation, by recursion on the first body:

```
Fixpoint anf_eq (G : list (V1 * V2)) (b1 : anf V1 bare) (b2 : anf V2 bare) {struct b1} : Prop :=
  match b1, b2 with
  | ALet _ e1 c1, ALet _ e2 c2 =>
      value_eq G e1 e2 /\ forall x1 x2, anf_eq ((x1, x2) :: G) (c1 x1) (c2 x2)
  | ARet a1, ARet a2 => atom_eq G a1 a2
  | _, _ => False
  end
```

`G` lists the pairs of variables in scope that correspond. Two variables are
related when `In (x1, x2) G` (`atom_eq`). Under a binder, the two bodies must
be related **for any** pair `(x1, x2)` added to `G`. This "for any" is what
makes the relation strong: you may open the two binders at whatever pair you
like.

### The graphs `gA`, `gW`, `gT`, `gD`

The proofs relate the master copy at `pv` to each projection with a `G` of a
special shape (TangentCorrect.v):

```
Definition gA (L : list pv) := map (fun p => (p, pa p)) L.
Definition gW (L : list pv) := map (fun p => (p, pw p)) L.
Definition gT (L : list pv) := map (fun p => (p, pt p)) L.
Definition gD (L : list pv) := map (fun p => (p, pd p)) L.
```

`gA L` is the graph of the function `pa` restricted to `L`, the variables in
scope. So almost every simulation lemma starts like this:

```
anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD -> ...
```

Read it as: "`bA`, `bW`, `bT` and `bD` are the analysis, well_formed,
transformation and dual-evaluation instances of the master body `bP`, where
each variable `p` of `L` is seen as `pa p`, `pw p`, `pt p` and `pd p`."

### Walking through one let

Take the first let of the example, `let t1 = x * y in rest`, with `L`
containing `px` and `py` (the `pv` records of `x` and `y`). The hypothesis
`anf_eq (gD L) bP bD` unfolds to:
1. `value_eq (gD L) (AOp2 Mul (AVar px) (AVar py)) eD`, so `eD` is
   `AOp2 Mul (AVar (pd px)) (AVar (pd py))` (the lemma `atom_graph` turns
   `atom_eq (gD L) (AVar px) a` into `a = AVar (pd px)`);
2. `forall x1 x2, anf_eq ((x1, x2) :: gD L) (rest_P x1) (rest_D x2)`.

To go under the binder, a proof builds the `pv` record of `t1`, call it
`x`, with `pd x` the dual value of `x * y`, `pn x` the number of its
generated variable, and so on. It then instantiates (2) at `x1 := x` and
`x2 := pd x`. Now `(x, pd x) :: gD L` is exactly `gD (x :: L)`, so the
invariant has the same shape one let further, with `L` grown by one. Every
simulation proof of a let does this, for the four graphs at once. You will
see it as `HcA x (pa x)`, `HcD x (pd x)`, or `HbA ix _ sx _` for the two
binders of a fold.

---

## 4. The tangent proof, the simpler model

The tangent proof is complete. Read it first: the adjoint proof copies its
architecture.

### The chain of theorems

`tangent_mode_correct` composes four results:
1. `normalize_correct` (Correctness.v): where the source computes a value,
   in any domain, its A-normal form computes the same.
2. `duals_derive` (DualsDerive.v): where `f` is `defined`, it is
   differentiable, and evaluating it over dual numbers computes the
   derivative applied to `dx`.
3. `tangent_simulates_duals_with` (TangentTop.v): the *unsimplified*
   tangent function, run over the reals, gives the primal value and the
   tangent of the dual evaluation of `normalize f`, whatever the initial
   values of its output-only tangent parameters. It also says that this code
   is `good` (well scoped).
4. `simplify_correct_tapes` (SimplifyCorrect.v): `simplify` preserves the
   result of `good` code.

Notice the idea: the derivative is never mentioned in the simulation. The
generated code is compared to the **dual-number evaluation** of the source,
which is a program, not a mathematical object. `duals_derive` alone connects
dual numbers with Coquelicot's derivative.

### The simulation of a body: `sim_body`

The heart is `sim_body` (TangentCorrect.v), proved for all bodies by
`simulation` (TangentLoops.v):

```
Definition sim_body (bP : anf pv bare) : Prop :=
  forall L k c s wP pp m bA bW bT bD ty v,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
  ctx_ok L k c s wP pp (live_anf k bW) ty -> real_or_array ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  let '((ss, (ve, de)), c') :=
    open_pairs (tan W (option_map (amap pt) wP) (rebuild _ bT (annotate_body_t false m k bA))) c in
  (c <= c')%nat /\ has_type ty v /\ (varied_anf k bA = false -> zero v) /\
  res_vars L (fun p => live_anf k bW p \/ owner wP pp = Some p) c ve /\
  dot_vars L (fun p => live_anf k bW p \/ owner wP pp = Some p) c de /\
  exists s', run ss s = Some s' /\ frame c (inplace wP pp) s s' /\
             body_result ty (inplace wP pp) s' ve de v.
```

The hypotheses, in groups:
- the four instances are related (section 3);
- `ctx_ok`: the store `s` holds the primal value of every live variable of
  `L`, and its tangent when it has one (fields in DEFINITIONS.md);
- the body type-checks with type `ty`, and its dual evaluation gives `v`.

The conclusion is about `open_pairs (tan ...) c`. That is the code `tan`
generates for this body, with its fresh locals numbered from `c` on (see
below). It says:
- the numbering advances (`c <= c'`);
- the value has its type, and it is zero when the body is not varied (the
  activity analysis is sound);
- the expressions `ve` and `de` (value and tangent) read only what they
  may (`res_vars`, `dot_vars`);
- the statements `ss` run from `s` to some `s'` and change nothing old
  except the in-place storage (`frame`);
- `ve` and `de` evaluate in `s'` to the primal and the tangent of `v`
  (`body_result`).

### Numbering generated variables: `open_pairs`

The generated code binds its locals with `Fresh`. To run it, the evaluator
numbers them 0, 1, 2, .... `simplify` compares the first component of a
`W = nat * nat` variable and the evaluator compares the second.
`open_pairs` (Scoping.v) opens the binders with the pair `(c, c)`:

```
Fixpoint open_pairs {A : Type} (s : scoped W A) (k : nat) : A * nat :=
  match s with
  | Named _ f => open_pairs (f (k, k)) (S k)
  | Fresh _ f => open_pairs (f (k, k)) (S k)
  | Done a => (a, k)
  end.
```

So in a statement, `let '((ss, ...), c') := open_pairs (...) c in ...` reads
"the code generated here, whose fresh variables are numbered from `c` to
`c'`". A variable is `consistent` when its two numbers agree, and `below c v`
says it was opened before `c`, that is, it existed before the code under
study.

### Scoping and `simplify`

`simplify` is only correct on code where every variable read is in scope,
every assigned variable is writable, and every defined variable is new. This
discipline is the inductive `good sc wr ss` of Scoping.v (`sc` = in scope,
`wr` = writable). Two of its rules:

```
| GoodConstant sc wr t v e r :
    expr_ok sc e -> ~ In v sc -> consistent v ->
    good (v :: sc) wr r -> good sc wr (DDefine (DConstant t) v e :: r)
| GoodPush sc wr t e r :
    In t wr -> expr_ok sc e -> good sc wr r -> good sc wr (DPush t e :: r)
```

`scoping` (TangentGood.v) proves that tangent code is `good`.
`simplify_correct_tapes` (SimplifyCorrect.v) then proves that
`simplify` preserves the execution of `good` code, tapes included:

```
Theorem simplify_correct_tapes (g : dfunction) (args : list (val R))
  r ps ss k res :
  open_pairs (dfbody g W) 0 = (DBody r ps ss, k) ->
  Forall consistent (params ps) ->
  good (params ps) (params ps) ss ->
  exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map outs ss)))
    0 args = Some res ->
  exec_dfunction reals (simplify g) args = Some res.
```

---

## 5. The adjoint proof

### 5.1 Two sweeps and one invariant

Adjoint code has two parts. The **forward sweep** recomputes the primal
values the reverse sweep will need, and records on *tapes* the values that
are about to be overwritten. The **reverse sweep** visits the lets in reverse
order. For `let x = e`, it adds `∂e/∂a * x_bar` to the adjoint `a_bar` of each
operand `a`. For a body, `adj` (Adjoint.v) returns the pair (forward,
reverse). Here is the case of a let:

```
  | ALet a e b' =>
      let '(v, ac, c) := let_ann a in
      let t := type_of e in
      with_storage written e b' (fun n rec =>
        sbind (adj m (b' (open_let t n v rec)) seed) (fun '(fb, rb) =>
        sbind (if c then fwd_value m e t n rec else Done []) (fun fe =>
        sbind (if ac then rev_value e t n else Done []) (fun re =>
        Done (app fe fb, app (if ac then bar_declaration t n else []) (app rb re))))))
```

The let is computed forward only if its annotation says *computed* (`c`).
It is transposed only if it is *active* (`ac`). The forward code is
`fe ++ fb` (this let, then the rest), and the reverse code is
`bar_declaration ++ rb ++ re` (declare `x_bar`, run the rest backward, then
transpose this let). In our example, no let is computed, so `fe` is always
empty, which matches the dump of section 1.

Which invariant does the proof follow? Not "the adjoints are correct": that
is a global statement about the whole function. The proof follows one real
number, the **pairing** (AdjointCorrect.v):

```
Definition pairing (O : owners) (s : store R) : R :=
  fold_right (fun '(t, n) acc => inner t (barv s n) + acc) 0 O.
```

`O : owners` is a list of pairs (tangent `t`, storage `n`). The pairing is
Σ ⟨t, adjoint of n in s⟩. Here `t` is the tangent, in direction `dx`, of the
variable that `n` holds, taken from the dual evaluation `pd`. Why this
number? Transposing `x = e` moves `x_bar` to the operands, weighted by the
partial derivatives. The tangent of `x` is the same combination of the
tangents of the operands. So the pairing does not change. At the end of the
function, the pairing is ⟨dx, g⟩, and at the start it was ⟨df · dx, yb⟩:
that is the dot-product test.

For our example, with `t3_bar = yb` at the start, the pairing is
`t3_dot * yb`. After transposing `t3 = t1 + t2`, it is
`t1_dot * t1_bar + t2_dot * t2_bar`, which is equal because
`t3_dot = t1_dot + t2_dot`, and so on down to
`x_dot * x_bar + y_dot * y_bar`.

### 5.2 `asim_body`: the shape of every adjoint lemma

`asim_body` (AdjointCorrect.v) is to the adjoint what `sim_body` is to the
tangent. One lemma covers both sweeps of a body:

```
Definition asim_body (bP : anf pv bare) : Prop :=
  forall L k c s wP pp m bA bW bT bD ty v se vo,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
  actx L k c s wP pp (live_anf k bW) (tbr cv m k bA) ty -> real_or_array ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  (m = Forward -> pp = PTop /\ (vo = None <-> cv = false) /\
                  (forall y, vo = Some (AWrites y) -> option_map (amap pt) wP = Some y) /\
                  (forall t, vo = Some (AReturns t) -> wP = None)) ->
  (m = Forward -> forall p, In p L -> live_anf k bW p -> vo_target vo <> Some (stored p)) ->
  (m = Forward -> forall t, vo_target vo = Some t -> below c t /\ consistent t /\ is_primal t) ->
  (m = Replay -> pp <> PTop) ->
  (m = Forward -> cv = true -> forall o, owner wP pp = Some o -> avaried (pa o) = false) ->
  let '((fw, rv), c') :=
    open_pairs (adj W (option_map (amap pt) wP) vo m (rebuild _ bT (annotate_body_t cv m k bA)) se) c in
  (c <= c')%nat /\ has_type ty v /\
  exists s1, run fw s = Some s1 /\
    fwd_frame c (inplace wP pp) (if sweep_eqb m Forward then vo else None) s s1 /\ tkeep c (inplace wP pp) s s1 /\
    (m = Forward -> vo_result vo v s1) /\
    forall s2 O, agree_prim c' (inplace wP pp) s1 s2 -> rctx L c wP pp O (useful cv m k bA) s2 ->
      seed_ok c ty se s2 -> tapes_ok L s2 ->
      (forall ix sx n0, pp = PArray ix sx -> inplace wP pp = Some n0 ->
         tail_tape k L bP bA bD s2 n0) ->
      exists s3, run rv s2 = Some s3 /\ (m = Forward -> vo_kept vo s2 s3) /\
        same_ex pp wP s s3 /\ tkeep c (inplace wP pp) s2 s3 /\
        rev_frame c (inplace wP pp) O s2 s3 /\
        (forall t n, In (t, n) O -> shaped t (barv s3 n)) /\
        pairing O s3 = result_pairing O ty (inplace wP pp) v se s2 /\
        tail_back k bA bD wP pp ty s2 s3.
```

Section 6 annotates it hypothesis by hypothesis. Its overall shape is:
"the forward code runs from `s` to `s1`; then, for **any** store `s2` that
agrees with `s1` on the primal keys, the reverse code runs from `s2` to `s3`,
and the pairing changes by the tangent of the body times the seed `se`."
The quantification over `s2` is what lets the proof of a let put the reverse
code of the rest *between* the forward code of this let and its own reverse
code.

### 5.3 Contexts: `actx`, `sctx`, `rctx`

Three records carry the invariants. Their fields are listed in DEFINITIONS.md
("The adjoint contexts"). Here is what each is for:
- `sctx` holds the facts that do not mention the store. Every variable of
  `L` is `static_ok` (the four instances agree on it), identities are
  unique, and the in-place place is sane (`place_ok`). It is shared with the
  tangent proof.
- `actx` is the context of the **forward** sweep. Its key field is
  `a_store`: every variable that the TBR analysis marks *to be recorded*
  (`tb`) has its primal value in the store. This is what makes the reverse
  sweep able to read it.
- `rctx` is the context of the **reverse** sweep, on the owners `O`. Its key
  field is `r_useful`: every useful, varied variable in scope is an owner,
  with its tangent.

```
Record rctx (L : list pv) (c : nat) (wP : option (atom pv)) (pp : pplace) (O : owners)
  (use : pv -> Prop) (s : store R) : Prop := {
  r_nodup : NoDup (map snd O);
  r_shape : forall t n, In (t, n) O -> shaped t (barv s n);
  r_below : forall t n, In (t, n) O -> exists j, n = DBound (j, j) /\ (j < c)%nat;
  r_useful : forall p, In p L -> use p -> avaried (pa p) = true -> In (tangent (pd p), stored p) O;
  r_value : forall p t, In p L -> use p -> In (t, stored p) O -> t = tangent (pd p);
  r_owner : forall o, owner wP pp = Some o -> In (tangent (pd o), stored o) O;
  r_args : forall p ny r, In p L -> varg (pw p) = Some (ny, r) -> avaried (pa p) = varied_role r;
  r_written : forall y, wP = Some (AVar y) -> exists ny r, varg (pw y) = Some (ny, r) /\ written_role r = true
}.
```

### 5.4 Places, owners and storage

Arrays are updated **in place**: `ASet a i v` does not allocate a new array,
it writes into the storage of `a`. The proofs track where this storage is
with a *place* (TangentCorrect.v):

```
Inductive pplace : Type :=
| PTop | PBranch | PScalar
| PArray (ix sx : pv).
```

`PTop` is the body of the function. `PArray ix sx` is the body of a fold
that updates an array in place, with loop index `ix` and state `sx`. The
**owner** is the variable whose storage the body may overwrite: the written
argument at the top, and the state `sx` inside an in-place loop:

```
Definition owner (wP : option (atom pv)) (pp : pplace) : option pv :=
  match pp, wP with
  | PTop, Some (AVar y) => match vty (pw y) with Array _ => Some y | _ => None end
  | PArray _ sx, _ => Some sx
  | _, _ => None
  end.

Definition inplace (wP : option (atom pv)) (pp : pplace) : option (dvar W) :=
  option_map stored (owner wP pp).
```

`inplace wP pp` appears as an exception in every frame predicate:
`frame c (inplace wP pp) s s'` means "nothing old changes, except the
in-place storage".

### 5.5 Tapes

When a loop overwrites a value that the reverse loop needs, the forward loop
pushes the old value on a tape, and the reverse loop pops it back. Here is
the real output for a product of the elements of `x`, `fold (nat 0) (nat 3)
(num "1") i\ acc\ op2 mul acc (get x i)` (case `07-fold-product`,
`dump -- derivative adjoint`):

```
prodx_adjoint(x: const ref real[3], x_bar: ref real[3], result_bar: real):
    var real t1 = 1
    tape t1_tape
    for i2 in [0, 3):
        push t1 onto t1_tape
        const real t3 = x[i2]
        const real t4 = t1 * t3
        t1 := t4
    var real t1_bar = 0
    t1_bar += result_bar
    for i5 in [0, 3) downward:
        t1 := pop t1_tape
        const real t7 = x[i5]
        const real r6_bar = t1_bar
        t1_bar := 0
        var real t7_bar = 0
        var real t8_bar = 0
        t8_bar += r6_bar
        t1_bar += t7 * t8_bar
        t7_bar += t1 * t8_bar
        x_bar[i5] += t7_bar
```

The reverse loop *replays* the body (it recomputes `t7 = x[i5]`) before
transposing it. The partial derivative of `acc * x[i]` with respect to
`x[i]` reads `acc`, so the state is *live* in the reverse loop and is pushed
before each step. The annotation says so: `[state varied, state recorded,
records]`.

The proofs describe tapes with:
- `fold_trace`: the list of the states of a fold before each step;
- `fold_tape`: what the tape holds after the forward sweep;
- `body_pushes` / `fold_pushes`: what a step of an in-place fold pushes (the
  element it overwrites);
- `tail_tape`: the tape the body of an in-place loop receives from its loop;
- `tail_back`: what the reverse sweep of such a body gives back.

`tail_tape` takes the activity instance `bA` and the dual instance `bD` of
the body, and it follows a let only on the value that the let computes:

```
Fixpoint tail_tape (k : nat) (L : list pv) (b : anf pv bare)
  (bA : anf avar bare) (bD : anf (val (dual R)) bare) (s : store R)
  (n : dvar W) {struct b} : Prop :=
  match b, bA, bD with
  | ALet _ eP cP, ALet _ eA cA, ALet _ eD cD =>
      (ptail cP -> forall eW, value_eq (gW L) eP eW ->
         fold_tape k eA eW eD s n) /\
      (forall x, pa x = let_binder k eA ->
         aeval_value (duals reals) eD = Some (pd x) ->
         tail_tape (S k) (x :: L) (cP x) (cA (let_binder k eA)) (cD (pd x))
           s n)
  | _, _, _ => True
  end.
```

### 5.6 Body classes: why `straight`, `branchy`, `foldy`, `nesty`

The adjoint proof is not done for all bodies at once. It is done for growing
*classes* of bodies, one per milestone. Each class is a predicate on the
master body, and each comes with a theorem "every body of the class has an
`asim_body`":
- `straight` (AdjointCorrect.v, theorem `asim_straight`): lets of
  operations, reads `a[i]` and in-place sets;
- `branchy top` (AdjointBranch.v): adds branches, maps and
  scalar folds. The flag `top` says whether we are at the top of the
  function, since maps and folds are only allowed there;
- `foldy top` (AdjointFoldy.v): adds folds that update an array in place,
  whose step is an `abody`, that is, ops and reads ending with a set
  (AdjointBranch.v). It is now a subclass of `nesty` (`foldy_nesty`), which
  carries its theorem;
- `nesty top` (AdjointNesty.v, `asim_nesty`): adds nests of any depth, an
  in-place fold whose step is an `nbody`, that is, ops and reads ending with
  a set, with an inner in-place fold on its state whose steps are again
  nbodies, or with the state itself (AdjointNBody.v).

Here is `branchy`, to see the pattern:

```
Fixpoint branchy (top : bool) (b : anf pv bare) : Prop :=
  match b with
  | ALet _ e b' => branchy_value top e /\ forall x, branchy top (b' x)
  | ARet _ => True
  end
with branchy_value (top : bool) (e : value pv bare) : Prop :=
  match e with
  | AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => True
  | ASet _ _ _ => top = true
  | AIte _ t e => branchy false t /\ branchy false e
  | AMap _ _ b => top = true /\ forall x, branchy false (b x)
  | AFold _ _ _ init b =>
      top = true /\ (forall p, init = AVar p -> ~ is_array (vty (pw p))) /\ forall x y, branchy false (b x y)
  end.
```

Why classes, instead of one proof for everything? Each new construct needs
new invariants: tapes for folds, in-place storage for arrays, the "dead outer
state" argument for nests. A class lets each milestone be closed and checked
before the next one starts. The price is M7: one must show that every
well-formed program belongs to the last class.

The classes are nested: `straight_branchy`, `branchy_foldy` (AdjointFoldy.v)
and `foldy_nesty` (AdjointTop.v) show that each class is included in the
next. So only the largest class needs its own theorem: `adjoint_nesty_duals`
(AdjointTop.v) goes through `adjoint_simulates_duals`, which needs only the
`asim_body` of the opened body, given by `asim_nesty`. The corollaries for
the smaller classes (`adjoint_straight_duals`, `adjoint_branchy_duals`,
`adjoint_foldy_duals`) follow from it by these inclusions.

### 5.7 The pieces of a value: `asim_fwd`, `asim_rev`, `psim_body`

`asim_body` of a let is proved from facts about its value (`asim_let`,
AdjointCorrect.v):
- `asim_fwd`: the forward code `fwd_value` stores the primal value;
- `asim_rev`: the reverse code `rev_value` keeps the pairing, with `n` now
  owning the tangent of the value;
- `act_value`: the value has its type, and it is zero when not varied;
- `act_owner`, `inplace_only`: facts about in-place values.

Inside loops and branches, the forward code is `prim`, which computes every
let without recording anything. `psim_body` (AdjointBranch.v) is its
simulation. You will see these names in the conclusions of `asim_branchy`
and `asim_nesty`.

---

## 6. Reading one real lemma end to end

### A small one: `tail_fold_state_ret`

```
Lemma tail_fold_state_ret k a eA cA :
  cA (let_binder k eA) = ARet (AVar (let_binder k eA)) ->
  tail_fold_state k (ALet a eA cA) =
  match eA with
  | AFold _ _ _ initA bA =>
      if varied_value k eA then Some (fold_live cv k initA bA) else None
  | _ => None
  end.
Proof.
move=> E; rewrite /= E.
case: eA E => //= ? ? ? initA bA E.
by rewrite E Nat.eqb_refl.
Qed.
```

How to read it:
- The variables `k a eA cA` are the next identity, the annotation, the
  value of the let (at `avar`, the instance of the analyses) and its
  continuation.
- The hypothesis says that the continuation, opened at the let's binder
  (`let_binder k eA`), just returns that binder. In other words the let is
  the **tail** of the body: `let x = e in x`.
- `tail_fold_state` (AdjointCorrect.v) asks: "does this body end with a
  varied fold, and is its innermost fold live?". The lemma computes the
  answer for a tail let: if the value is a fold, the answer is its
  `fold_live` when the fold is varied, and `None` otherwise.
- Why it is there: `tail_back`, the conclusion of `asim_body` about the
  storage, is stated with `tail_fold_state`. This lemma is the bridge from a
  let that ends a body to the fold it contains.
- The proof: `move=> E` names the hypothesis, `rewrite /= E` unfolds
  `tail_fold_state` one step and uses `E`, `case: eA E` splits on the value,
  `//=` closes the non-fold cases, and the fold case ends with
  `Nat.eqb_refl` (the binder's identity equals `k`).

### A big one: the hypotheses of `asim_body`

Let us annotate the statement of section 5.2:
- `forall L k c s wP pp m bA bW bT bD ty v se vo`: the variables in scope,
  the next identity, the next generated number, the store, the written
  argument, the place, the sweep (`Forward` or `Replay`), the four instances,
  the type, the dual value, the seed (the expression of the adjoint of the
  body's value), and what adjoint-value must output.
- The four `anf_eq`: section 3.
- `actx L k c s wP pp (live_anf k bW) (tbr cv m k bA) ty`: the forward
  context. The variables of `L` that the body reads (`live_anf`) have the
  right types, and those that its adjoint code reads (`tbr`, to be recorded)
  are in the store.
- `real_or_array ty` and `typecheck ... = (ty, Ok)`: the body is well
  typed, and its value is a real or an array (it carries an adjoint).
- `aeval (duals reals) bD = Some v`: its dual evaluation succeeds with `v`.
- The five hypotheses starting with `m = Forward ->` or `m = Replay ->` are
  side conditions on the sweep. The forward sweep happens at the top only,
  and adjoint-value's output target is a fresh primal key that no live
  variable uses. A replay never happens at the top.
- In the conclusion, the hypotheses of the reverse part are:
  - `agree_prim`: `s2` agrees with `s1` on the primal keys and tapes;
  - `rctx ... O (useful cv m k bA) s2`: the owners are in place;
  - `seed_ok`: the seed reads only old keys;
  - `tapes_ok`: the recorded variables have tapes;
  - `tail_tape`: inside an in-place loop, the tape the loop provides.
- The conclusions of the reverse part: it terminates (`run rv s2 = Some
  s3`), it changes only adjoints and owned storage (`rev_frame`, `tkeep`,
  `same_ex`), the owners stay well shaped, the pairing changes as it should
  (`result_pairing`), and `tail_back` says what happens to the in-place
  storage.

A good way to learn a statement like this one is to find the place where it
is *used*. Grep for `asim_body` in AdjointTop.v to see how
`adjoint_simulates_duals` instantiates each hypothesis at the top of a
function.

---

## 7. Reading the proof scripts

Most proof files use the ssreflect tactic language on Stdlib types (no
mathcomp library). Each starts with:

```
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".
```

The second line makes bullets mere markers, so a script may bullet the easy
cases and continue the last case unbulleted. The conventions are described in
[SSREFLECT_STYLE.md](SSREFLECT_STYLE.md). Here are the idioms you will meet,
on real excerpts.

### A complete small proof: `act_ret` (AdjointBranch.v)

```
Lemma act_ret (aP : atom pv) : act_body (ARet aP).
Proof.
move=> L k wP pp [? ? ? | aA] [? ? ? | aW] [? ? ? | aD] //= ty v.
move=> /atom_graph [-> Hin] /atom_graph [-> _] /atom_graph [-> _] HL Htc Hev.
have H1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
have Ety : ty = of_atom (amap pw aP).
  move: Htc; case: aP {Hin H1 Hev} => [p | s | z] /=; [| by case | by case].
  case: (varg (pw p)) => [[? ?] |] /=; last by case.
  by case: (_ && _) => -[].
subst ty; split; first exact: atom_type k aP v H1 Hev.
by move=> Hv; exact: atom_zero k aP v H1 Hv Hev.
Qed.
```

- `move=> x y`: introduce. `[? ? ? | aA]` destructs the next variable (an
  `anf`) on the fly: `ALet` with three anonymous fields, or `ARet aA`.
- `//=`: simplify (`/=`), then close the trivial goals (`//`). Here it kills
  every case where one instance is a `let` and another a `ret`, since
  `anf_eq` is then `False`.
- `/atom_graph [-> Hin]`: apply the *view* `atom_graph` to the hypothesis
  being introduced, then destruct the result. `->` rewrites with the
  equality in the goal. Beware: an ssreflect `->` rewrites the goal only.
- `have H1 : P.` followed by an indented proof ending in `by ...`: a local
  lemma. The one-line form is `have H : P by tac.`
- `case: aP {Hin H1 Hev} => [p | s | z]`: case analysis on `aP`, clearing
  three hypotheses first, naming the fields of each constructor.
- `[| by case | by case]`: one tactic per generated goal.
- `last by case`, `first exact: ...`: act on the last or the first goal.
- `exact: lem args`, `apply: lem`: like `exact`/`apply`, with better
  unification of the arguments you leave out.
- `-[]` in `=> -[]`: destruct the hypothesis in front of you, here an
  equation between pairs, which discharges a contradictory case.

### Named case analysis: `case E: (...)`

`case E: (e) H => [a | b] H.` performs a case analysis on the expression
`e`, keeps the equation `E : e = ...`, and reverts `H` first, so that `e` is
also replaced in `H`. It is how the scripts walk through a type-checker or an
evaluator. For example, in AdjointNBody.v:

```
case Ete: (typecheck_value _ _ _ _ _) Htc => [te []] //= Htc.
```

reads: "look at the result of `typecheck_value`, call it `(te, d)`, keep only
the case `d = Ok` (the others close by `//`), and give back the
specialized `Htc`".

### Rewriting and unfolding

- `rewrite /def` unfolds `def` (`unfold def`); `rewrite /def in H` does it in
  `H`.
- `rewrite L1 -L2 {}H`: rewrite left to right, then right to left. `{}H`
  rewrites with `H` and clears it.
- A conditional rewrite `rewrite (L _ Hx)` passes the premise. With
  `rewrite L`, the side conditions come **first**, before the main goal.

### Induction

`elim: tr z => [| st tr IH] z //=; rewrite IH.` is the whole proof of
`fold_pushes_fix`: induction on the list `tr`, generalizing `z`, naming the
head, tail and induction hypothesis, simplifying, then rewriting with the
hypothesis.

For the mutual types `anf`/`value`, the scripts use
`apply: (anf_value_ind pv bare (fun b => ...) (fun e => ...))`, which gives
one goal per constructor, in the order `ALet`, `ARet`, `AOp1`, `AOp2`,
`AGet`, `ASet`, `AIte`, `AMap`, `AFold`.

### Older Ltac style

Every proof file imports ssreflect, but some older proofs still use plain
Ltac tactics (`destruct`, `inversion`, `repeat match goal`), and a few Ltac
definitions remain. You will meet, for instance, this tactic of
AdjointCorrect.v, which destructs the four instances of a value and turns
every `atom_eq` into an equation:

```
Ltac act_intro :=
  let L := fresh "L" in let k := fresh "k" in
  intros L k wP pp tail eA eW eD te ve HA HW HD HL Htc Hev;
  destruct eA, eW, eD; simpl in HA, HW, HD; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.
```

It is worth understanding this one: its `repeat match goal` is the Ltac
version of "walk through one let" (section 3). The ssreflect files do the
same with `case:` and `move/atom_graph`.

---

## 8. A map of the files, in reading order

The order of `_CoqProject` is a valid reading order. Here it is by topic,
with when to read each file.

The languages and their semantics:
- `Syntax.v`, `Anf.v`, `Derivative.v`, `Target.v`: read first. They hold
  the inductive types of L0, L1/L1ᵃ, L2, L3.
- `Domain.v`, `Eval.v`, `EvalAnf.v`, `Exec.v`: read when a statement mentions
  `eval_function`, `aeval`, `run`, `exec_dfunction` or `store_get`.
- `Smooth.v`: read when you meet `defined` or `smooth_reals`.
- `Operations.v`: the table of operations and of their partial derivatives
  (`partial1`, `partial2`).

The passes (no proofs inside):
- `Normalize.v`, `WellFormed.v`: read `WellFormed.v` when a proof does a case
  analysis on `typecheck`; it says what the tool accepts.
- `Atoms.v`, `Activity.v`, `Tbr.v`, `Annotate.v`: the analyses. Read `Tbr.v`
  (`needs`) before any adjoint proof.
- `Transform.v`, `Tangent.v`, `Adjoint.v`: the transformations. Keep
  `Adjoint.v` open next to any adjoint proof; it is 274 lines.
- `Simplify.v`, `Scoping.v`, `Lower.v`, `Cxx.v`, `Gallina.v`, `Dump.v`,
  `Adjudge.v`: the back end and the driver.

The proofs:
- `Correctness.v`, `AnfEquiv.v`: parametricity, `normalize_correct`,
  `annotate_correct`. Read for section 3.
- `Euclidean.v`, `DualsDerive.v`: dual numbers compute derivatives. Read
  only if you care about the calculus.
- `SimplifyCorrect.v`: `simplify` is correct. Independent of the rest.
- `TangentCorrect.v`, `TangentLoops.v`, `TangentGood.v`, `TangentTop.v`,
  `TangentMode.v`: the tangent proof. Read `TangentCorrect.v` up to
  `sim_body` before anything adjoint; `pv`, the graphs and the contexts are
  defined there.
- `AdjointSpec.v`: the layout of the adjoint function's arguments and
  results.
- `AdjointCorrect.v`: pairing, contexts, `asim_body`, `asim_let`,
  operations, `asim_straight`.
- `AdjointBranch.v`: branches, maps, scalar folds, the class `branchy`.
- `AdjointFold.v`, `AdjointFoldy.v`: the pieces of in-place folds, `foldy`.
- `AdjointNBody.v`, `AdjointNesty.v`: nests of in-place folds of any depth
  (milestone M5b), ending in `asim_nesty`.
- `AdjointTop.v`: the top level, `adjoint_simulates_duals` and the four
  corollaries.
- `AdjointMode.v`: the statement of `adjoint_mode_correct` (`Admitted`).

### Exploring interactively

- `Print Assumptions tangent_mode_correct.` lists the axioms behind a result.
  Try it on `adjoint_nesty_duals` to check that it is closed.
- `About asim_body.` gives the type and the file of a name.
  `Print tail_tape.` prints a definition.
- `Search (anf_eq (gA _) _ _).` finds lemmas by pattern. `Search "tail" fold.`
  combines a name fragment and a constant.
- The passes compute. `Compute normalize f_fn.` is unreadable (PHOAS terms
  print as functions), but `Compute (main ModeAdjoint "f.elpi" [f_fn]).`
  prints the C++ header.
- If your editor talks to a rocq-mcp server, you can open a proof state at
  any lemma and try tactics without recompiling the file.

Build with `make` (Rocq 9.1). The logical directory is `ElpiDiff`, so
`From ElpiDiff Require Import AdjointCorrect.` works from a scratch file
compiled with `-R . ElpiDiff`.

---

## 9. Pointers

- [DEFINITIONS.md](DEFINITIONS.md): the glossary, concept by concept, then
  file by file. Read its section "Reading a statement: an example" after
  this tutorial. Note that its description of `tail_tape` predates the
  current form shown in section 5.5.
- [README.md](README.md): the theorems, the milestones of the adjoint proof,
  the file table, and how the Elpi constructs were translated.
- [BUGS.md](BUGS.md): the bugs of the tool that the proofs found, with the
  programs that triggered them. It is a good illustration of why each
  side condition of a statement is there.
- [SSREFLECT_STYLE.md](SSREFLECT_STYLE.md): the proof style.
- [tools/README.md](../tools/README.md): the test scripts that compare Rocq
  with Elpi and both with C++.
