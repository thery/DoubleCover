(* Correctness.v — the correctness theorems of the passes of elpiDiff, one
   section per stage, each against the evaluators.

   A closed program in PHOAS is a family of terms, one per type of variables
   (`fdef f V`); nothing in Rocq forces the members of the family to be the
   same term. A pass instantiates its input at one type and the evaluator at
   another, so a theorem may assume that the program is parametric: its
   instances are related, variable for variable. Stage 1 (normalize) does;
   stage 2 (annotate) does not, since it keeps the instance it is evaluated
   at and only replaces its annotations. *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Anf Domain Eval EvalAnf Normalize Annotate.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

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

Section NormalizeCorrect.
Variable N : Type.
Variable D : domain N.

(* The source is normalized with its variables as atoms (atom (val N)), and
   evaluated with its variables as values (val N): a pair of G is an atom and
   the value it evaluates to. *)
Definition env_ok (G : list (atom (val N) * val N)) : Prop :=
  forall a v, In (a, v) G -> aeval_atom D a = Some v.

Lemma env_ok_cons G a v :
  env_ok G -> aeval_atom D a = Some v -> env_ok ((a, v) :: G).
Proof. by move=> HG Ha a' v' [[<- <-] | /HG]. Qed.

Lemma env_ok_var G w : env_ok G -> env_ok ((AVar w, w) :: G).
Proof. by move=> HG; apply: env_ok_cons. Qed.

(* A map or a fold computes the same when its body computes the same, at
   least where the body of the source computes. *)
Lemma eval_map_sim (ev1 ev2 : val N -> option (val N)) :
  (forall w x, ev2 w = Some x -> ev1 w = Some x) ->
  forall n i xs, eval_map ev2 i n = Some xs -> eval_map ev1 i n = Some xs.
Proof.
move=> Hev; elim=> [| n IH] i xs //=.
case E: (ev2 (VInt i)) => [[x | | | |] |] //.
rewrite (Hev _ _ E).
case E': (eval_map ev2 (i + 1)%Z n) => [ys |] //.
by rewrite (IH _ _ E').
Qed.

Lemma eval_fold_sim (ev1 ev2 : val N -> val N -> option (val N)) :
  (forall w s x, ev2 w s = Some x -> ev1 w s = Some x) ->
  forall n i s x, eval_fold ev2 i n s = Some x -> eval_fold ev1 i n s = Some x.
Proof.
move=> Hev; elim=> [| n IH] i s x //=.
case E: (ev2 (VInt i) s) => [y |] // H.
by rewrite (Hev _ _ _ E); apply: IH.
Qed.

(* Unfolds the evaluation of the source, hypothesis by hypothesis. *)
Ltac inv_some :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H as H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : match ?e with _ => _ end = Some _ |- _ => destruct e eqn:?
  end.

(* The main lemma, for the continuation-passing norm: when the source t2
   evaluates to v, and the continuation k gives r on any atom whose value is v,
   the normal form of t1 gives r. *)
Lemma norm_sim G t1 t2 :
  term_equiv _ _ G t1 t2 -> env_ok G ->
  forall v, eval D t2 = Some v ->
  forall k r, (forall a, aeval_atom D a = Some v -> aeval D (k a) = r) ->
  aeval D (norm t1 k) = r.
Proof.
elim=> {G t1 t2} [G x1 x2 Hin | G s | G n | G f a1 a2 Ha IHa
  | G f a1 a2 b1 b2 Ha IHa Hb IHb | G a1 a2 i1 i2 Ha IHa Hi IHi
  | G a1 a2 i1 i2 v1 v2 Ha IHa Hi IHi Hv IHv
  | G e1 e2 b1 b2 He IHe Hb IHb
  | G c1 c2 t1 t2 e1 e2 Hc IHc Ht IHt He IHe
  | G lo1 lo2 hi1 hi2 b1 b2 Hlo IHlo Hhi IHhi Hb IHb
  | G lo1 lo2 hi1 hi2 init1 init2 b1 b2 Hlo IHlo Hhi IHhi Hinit IHinit Hb IHb]
  HG v Hev k r Hk; rewrite /= in Hev *; inv_some.
- (* Var *) exact/Hk/HG.
- (* Num *) by apply: Hk; rewrite /= Heqo.
- (* Nat *) exact: Hk.
- (* Op1 *) apply: (IHa HG _ erefl) => x_ Hx /=; rewrite Hx Hev.
  exact: Hk.
- (* Op2 *) apply: (IHa HG _ erefl) => x_ Hx.
  apply: (IHb HG _ erefl) => y_ Hy /=.
  by rewrite Hx Hy Hev; apply: Hk.
- (* Get *) apply: (IHa HG _ erefl) => x_ Hx.
  apply: (IHi HG _ erefl) => j_ Hj /=.
  by rewrite Hx Hj Heqo1; apply: Hk.
- (* Set *) apply: (IHa HG _ erefl) => x_ Hx.
  apply: (IHi HG _ erefl) => j_ Hj.
  apply: (IHv HG _ erefl) => w_ Hw /=.
  by rewrite Hx Hj Hw Heqo2; apply: Hk.
- (* Let *) apply: (IHe HG _ erefl) => a_ Ha.
  exact: (IHb a_ _ (env_ok_cons _ _ _ HG Ha) _ Hev _ _ Hk).
- (* Ite, then *) apply: (IHc HG _ erefl) => x_ Hx /=.
  rewrite Hx (IHt HG _ Hev (fun x => ARet x) _ (fun a Ha => Ha)).
  exact: Hk.
- (* Ite, else *) apply: (IHc HG _ erefl) => x_ Hx /=.
  rewrite Hx (IHe HG _ Hev (fun x => ARet x) _ (fun a Ha => Ha)).
  exact: Hk.
- (* Map *) apply: (IHlo HG _ erefl) => l_ Hl.
  apply: (IHhi HG _ erefl) => h_ Hh /=.
  rewrite Hl Hh (eval_map_sim _ (fun w => eval D (b2 w)) _ _ _ _ Heqo1).
    by move=> w x Hw; apply: (IHb _ _ (env_ok_var _ _ HG) _ Hw).
  exact: Hk.
(* Fold *)
apply: (IHlo HG _ erefl) => l_ Hl.
apply: (IHhi HG _ erefl) => h_ Hh.
apply: (IHinit HG _ erefl) => x_ Hx /=.
rewrite Hl Hh Hx (eval_fold_sim _ (fun w s => eval D (b2 w s)) _ _ _ _ _ Hev).
  move=> w s y Hw.
  have HGws := env_ok_var _ _ (env_ok_var _ _ HG).
  by apply: (IHb _ _ _ _ (HGws w s) _ Hw).
exact: Hk.
Qed.

Lemma normalize_definition_sim G d1 d2 :
  definition_equiv _ _ G d1 d2 -> env_ok G ->
  forall args v, eval_definition D d2 args = Some v ->
  aeval_definition D (normalize_definition d1) args = Some v.
Proof.
elim=> {G d1 d2} [G n t r f1 f2 Hf IHf | G r1 r2 b1 b2 Hr Hb] HG args v Hev.
  case: args Hev => [| a args] //= Hev.
  exact: (IHf _ _ (env_ok_var _ _ HG) _ _ Hev).
case: args Hev => [| a args] //= Hev.
by apply: (norm_sim _ _ _ Hb HG _ Hev).
Qed.

End NormalizeCorrect.

Theorem normalize_correct :
  forall (N : Type) (D : domain N) (f : function) (args : list (val N)) (v : val N),
    parametric f ->
    eval_function D f args = Some v ->
    aeval_function D (normalize f) args = Some v.
Proof.
move=> N D f args v Hf Hev.
apply: (normalize_definition_sim N D [] _ _ (Hf _ _) _ args v Hev).
by move=> a w [].
Qed.

(* ---------------------------------------------------------------------------
   Stage 2: annotate, from L1 to L1ᵃ.

   On any arguments and in any domain of numbers, the annotated function
   computes exactly what the function computes, failures included: annotate
   evaluates the instance `afdef a (val N)` itself, only with new annotations
   (rebuild), and the evaluator ignores the annotations. The tree of
   annotations is computed from another instance (at avar), but rebuild
   accepts any tree, falling back to no annotation where the tree does not
   follow the body: so no parametricity is needed, and the theorem is an
   equality. *)

Scheme anf_ind' := Induction for anf Sort Prop
  with value_ind' := Induction for value Sort Prop.
Combined Scheme anf_value_ind from anf_ind', value_ind'.

Section AnnotateCorrect.
Variable N : Type.
Variable D : domain N.

(* A map or a fold computes the same when its body computes the same
   everywhere (proved by induction on the count, without functional
   extensionality). *)
Lemma eval_map_ext (ev1 ev2 : val N -> option (val N)) :
  (forall w, ev1 w = ev2 w) -> forall n i, eval_map ev1 i n = eval_map ev2 i n.
Proof. by move=> Hev; elim=> [| n IH] i //=; rewrite Hev IH. Qed.

Lemma eval_fold_ext (ev1 ev2 : val N -> val N -> option (val N)) :
  (forall w s, ev1 w s = ev2 w s) -> forall n i s, eval_fold ev1 i n s = eval_fold ev2 i n s.
Proof.
by move=> Hev; elim=> [| n IH] i s //=; rewrite Hev; case: (ev2 (VInt i) s).
Qed.

(* A body, and a value, rebuilt with any tree of annotations, evaluate as
   before. *)
Lemma rebuild_eval :
  (forall b : anf (val N) bare, forall t, aeval D (rebuild _ b t) = aeval D b) /\
  (forall e : value (val N) bare, forall t, aeval_value D (rebuild_value _ e t) = aeval_value D e).
Proof.
apply: anf_value_ind => //.
- (* ALet *) move=> [] e IHe b IHb [a vt rest |] /=; rewrite IHe;
    by case: (aeval_value D e).
- (* AIte *) by move=> c t IHt e IHe [| t1 e1 | bt | a bt] /=; rewrite IHt IHe.
- (* AMap *) move=> lo hi b IHb vt.
  have H : forall bt, aeval_value D (rebuild_value _ (AMap lo hi b) (TMap bt))
                       = aeval_value D (AMap lo hi b).
    move=> bt /=.
    case: (aeval_atom D lo) => [[] |] //; case: (aeval_atom D hi) => [[] |] //.
    by move=> *; rewrite (eval_map_ext _ (fun v => aeval D (b v))).
  by case: vt => *; try apply: H; exact: (H TRet).
(* AFold *)
move=> [] lo hi init b IHb vt.
have H : forall a bt,
    aeval_value D (AFold a lo hi init (fun i s => rebuild _ (b i s) bt))
    = aeval_value D (AFold Bare lo hi init b).
  move=> a bt /=.
  case: (aeval_atom D lo) => [[] |] //; case: (aeval_atom D hi) => [[] |] //.
  by move=> *; case: (aeval_atom D init) => // *; apply: eval_fold_ext.
by case: vt => *; apply: H.
Qed.

Lemma rebuild_definition_eval (d : adefinition (val N) bare) t args :
  aeval_definition D (rebuild_definition _ d t) args = aeval_definition D d args.
Proof.
elim: d t args => [n ty r f IHf | r b] t [| a args] //=.
exact: (proj1 rebuild_eval).
Qed.

End AnnotateCorrect.

Theorem annotate_correct :
  forall (N : Type) (D : domain N) (cv : bool) (a : afunction bare) (args : list (val N)),
    aeval_function D (annotate cv a) args = aeval_function D a args.
Proof. by move=> N D cv a args; apply: rebuild_definition_eval. Qed.
