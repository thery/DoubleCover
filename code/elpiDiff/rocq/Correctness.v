(* Correctness.v — the correctness theorems of the passes of elpiDiff, stated
   (not yet proved), one section per stage, each against the evaluators.

   A closed program in PHOAS is a family of terms, one per type of variables
   (`fdef f V`); nothing in Rocq forces the members of the family to be the
   same term. A pass instantiates its input at one type and the evaluator at
   another, so the theorems assume that the program is parametric: its
   instances are related, variable for variable. *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Anf Domain Eval EvalAnf Normalize.

Import ListNotations.

(* ---------------------------------------------------------------------------
   Parametricity of a source program (L0). `term_equiv G t1 t2`: t1 and t2 are
   the same term, where the variables paired in G correspond. *)

Section Equiv.
Variables V1 V2 : Type.

Inductive term_equiv (G : list (V1 * V2)) : term V1 -> term V2 -> Prop :=
| EqVar x1 x2 : In (x1, x2) G -> term_equiv G (Var x1) (Var x2)
| EqNum s : term_equiv G (Num s) (Num s)
| EqNat k : term_equiv G (Nat k) (Nat k)
| EqOp1 f a1 a2 : term_equiv G a1 a2 -> term_equiv G (Op1 f a1) (Op1 f a2)
| EqOp2 f a1 a2 b1 b2 :
    term_equiv G a1 a2 -> term_equiv G b1 b2 -> term_equiv G (Op2 f a1 b1) (Op2 f a2 b2)
| EqGet a1 a2 i1 i2 :
    term_equiv G a1 a2 -> term_equiv G i1 i2 -> term_equiv G (Get a1 i1) (Get a2 i2)
| EqSet a1 a2 i1 i2 v1 v2 :
    term_equiv G a1 a2 -> term_equiv G i1 i2 -> term_equiv G v1 v2 ->
    term_equiv G (Set_ a1 i1 v1) (Set_ a2 i2 v2)
| EqLet e1 e2 b1 b2 :
    term_equiv G e1 e2 ->
    (forall x1 x2, term_equiv ((x1, x2) :: G) (b1 x1) (b2 x2)) ->
    term_equiv G (Let_ e1 b1) (Let_ e2 b2)
| EqIte c1 c2 t1 t2 e1 e2 :
    term_equiv G c1 c2 -> term_equiv G t1 t2 -> term_equiv G e1 e2 ->
    term_equiv G (Ite c1 t1 e1) (Ite c2 t2 e2)
| EqMap lo1 lo2 hi1 hi2 b1 b2 :
    term_equiv G lo1 lo2 -> term_equiv G hi1 hi2 ->
    (forall i1 i2, term_equiv ((i1, i2) :: G) (b1 i1) (b2 i2)) ->
    term_equiv G (Map lo1 hi1 b1) (Map lo2 hi2 b2)
| EqFold lo1 lo2 hi1 hi2 init1 init2 b1 b2 :
    term_equiv G lo1 lo2 -> term_equiv G hi1 hi2 -> term_equiv G init1 init2 ->
    (forall i1 i2 s1 s2, term_equiv ((s1, s2) :: (i1, i2) :: G) (b1 i1 s1) (b2 i2 s2)) ->
    term_equiv G (Fold lo1 hi1 init1 b1) (Fold lo2 hi2 init2 b2).

Inductive result_equiv (G : list (V1 * V2)) : result V1 -> result V2 -> Prop :=
| EqReturns t : result_equiv G (Returns t) (Returns t)
| EqWrites y1 y2 : term_equiv G y1 y2 -> result_equiv G (Writes y1) (Writes y2).

Inductive definition_equiv (G : list (V1 * V2)) : definition V1 -> definition V2 -> Prop :=
| EqArg n t r f1 f2 :
    (forall x1 x2, definition_equiv ((x1, x2) :: G) (f1 x1) (f2 x2)) ->
    definition_equiv G (Arg n t r f1) (Arg n t r f2)
| EqBody r1 r2 b1 b2 :
    result_equiv G r1 r2 -> term_equiv G b1 b2 ->
    definition_equiv G (Body r1 b1) (Body r2 b2).

End Equiv.

(* A source function is parametric: any two of its instances are related. *)
Definition parametric (f : function) : Prop :=
  forall V1 V2, definition_equiv V1 V2 [] (fdef f V1) (fdef f V2).

(* ---------------------------------------------------------------------------
   Stage 1: normalize, from L0 to L1 (A-normal form).

   On any arguments and in any domain of numbers, when the source computes a
   value, its A-normal form computes the same value: normalize names the
   intermediate values without reordering what is evaluated, and a branch, a
   map or a fold body stays a body.

   The converse fails only on a literal the domain cannot read, bound and never
   used: `let x = Num "abc" in 1` fails in L0, which evaluates the let, while
   its A-normal form, `ARet (ANum "1")`, gives 1, since a literal is an atom
   and is read only where it is used. *)

Theorem normalize_correct :
  forall (N : Type) (D : domain N) (f : function) (args : list (val N)) (v : val N),
    parametric f ->
    eval_function D f args = Some v ->
    aeval_function D (normalize f) args = Some v.
Admitted.
