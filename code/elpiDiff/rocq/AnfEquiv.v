(* AnfEquiv.v — parametricity of the programs of L1, for the correctness of
   the transformations.

   A pass instantiates a closed program of L1 at the type of variables it
   needs: annotate at avar, well_formed at vinfo, tangent at tvar, the
   evaluator at values. To relate what they compute, the instances must be
   the same term, variable for variable: `anf_eq G b1 b2`, where G pairs the
   variables in scope that correspond (as `term_equiv` of Correctness.v for
   L0). It is defined by recursion on b1: a binder relates its two bodies on
   any pair of variables, added to G.

   `normalize_parametric`: the normal form of a parametric source program is
   parametric, its instances related at any two types. *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Anf Normalize Correctness.

Import ListNotations.

Section AnfEq.
Variables V1 V2 : Type.

Definition atom_eq (G : list (V1 * V2)) (a1 : atom V1) (a2 : atom V2) : Prop :=
  match a1, a2 with
  | AVar x1, AVar x2 => In (x1, x2) G
  | ANum s1, ANum s2 => s1 = s2
  | ANat k1, ANat k2 => k1 = k2
  | _, _ => False
  end.

Fixpoint anf_eq (G : list (V1 * V2)) (b1 : anf V1 bare) (b2 : anf V2 bare) {struct b1} : Prop :=
  match b1, b2 with
  | ALet _ e1 c1, ALet _ e2 c2 =>
      value_eq G e1 e2 /\ forall x1 x2, anf_eq ((x1, x2) :: G) (c1 x1) (c2 x2)
  | ARet a1, ARet a2 => atom_eq G a1 a2
  | _, _ => False
  end
with value_eq (G : list (V1 * V2)) (e1 : value V1 bare) (e2 : value V2 bare) {struct e1} : Prop :=
  match e1, e2 with
  | AOp1 f1 a1, AOp1 f2 a2 => f1 = f2 /\ atom_eq G a1 a2
  | AOp2 f1 a1 b1, AOp2 f2 a2 b2 => f1 = f2 /\ atom_eq G a1 a2 /\ atom_eq G b1 b2
  | AGet a1 i1, AGet a2 i2 => atom_eq G a1 a2 /\ atom_eq G i1 i2
  | ASet a1 i1 v1, ASet a2 i2 v2 => atom_eq G a1 a2 /\ atom_eq G i1 i2 /\ atom_eq G v1 v2
  | AIte c1 t1 e1, AIte c2 t2 e2 => atom_eq G c1 c2 /\ anf_eq G t1 t2 /\ anf_eq G e1 e2
  | AMap lo1 hi1 b1, AMap lo2 hi2 b2 =>
      atom_eq G lo1 lo2 /\ atom_eq G hi1 hi2 /\
      forall i1 i2, anf_eq ((i1, i2) :: G) (b1 i1) (b2 i2)
  | AFold _ lo1 hi1 init1 b1, AFold _ lo2 hi2 init2 b2 =>
      atom_eq G lo1 lo2 /\ atom_eq G hi1 hi2 /\ atom_eq G init1 init2 /\
      forall i1 i2 s1 s2, anf_eq ((s1, s2) :: (i1, i2) :: G) (b1 i1 s1) (b2 i2 s2)
  | _, _ => False
  end.

Definition aresult_eq (G : list (V1 * V2)) (r1 : aresult V1) (r2 : aresult V2) : Prop :=
  match r1, r2 with
  | AReturns t1, AReturns t2 => t1 = t2
  | AWrites y1, AWrites y2 => atom_eq G y1 y2
  | _, _ => False
  end.

Fixpoint adefinition_eq (G : list (V1 * V2)) (d1 : adefinition V1 bare) (d2 : adefinition V2 bare)
  {struct d1} : Prop :=
  match d1, d2 with
  | AArg n1 t1 r1 f1, AArg n2 t2 r2 f2 =>
      n1 = n2 /\ t1 = t2 /\ r1 = r2 /\ forall x1 x2, adefinition_eq ((x1, x2) :: G) (f1 x1) (f2 x2)
  | ABody r1 b1, ABody r2 b2 => aresult_eq G r1 r2 /\ anf_eq G b1 b2
  | _, _ => False
  end.

(* A related pair of atoms stays related in a larger context. *)
Lemma atom_eq_incl G H a1 a2 : incl G H -> atom_eq G a1 a2 -> atom_eq H a1 a2.
Proof. destruct a1, a2; simpl; auto. Qed.

End AnfEq.

Arguments atom_eq {V1 V2}.  Arguments anf_eq {V1 V2}.  Arguments value_eq {V1 V2}.
Arguments aresult_eq {V1 V2}.  Arguments adefinition_eq {V1 V2}.

(* ---------------------------------------------------------------------------
   normalize keeps parametricity. The source is normalized with its variables
   as atoms; a pair of the context of the source is a pair of related atoms. *)

Section NormalizeEq.
Variables V1 V2 : Type.

(* The main lemma, for the continuation-passing norm: related sources, with
   continuations related on related atoms (in any larger context: norm adds
   binders), give related normal forms. *)
Lemma norm_eq (G : list (atom V1 * atom V2)) t1 t2 :
  term_equiv _ _ G t1 t2 ->
  forall H, (forall a1 a2, In (a1, a2) G -> atom_eq H a1 a2) ->
  forall k1 k2, (forall H' a1 a2, incl H H' -> atom_eq H' a1 a2 -> anf_eq H' (k1 a1) (k2 a2)) ->
  anf_eq H (norm t1 k1) (norm t2 k2).
Proof.
  induction 1 as [G x1 x2 Hin | G s | G n | G f a1 a2 Ha IHa
                 | G f a1 a2 b1 b2 Ha IHa Hb IHb | G a1 a2 i1 i2 Ha IHa Hi IHi
                 | G a1 a2 i1 i2 v1 v2 Ha IHa Hi IHi Hv IHv
                 | G e1 e2 b1 b2 He IHe Hb IHb
                 | G c1 c2 t1 t2 e1 e2 Hc IHc Ht IHt He IHe
                 | G lo1 lo2 hi1 hi2 b1 b2 Hlo IHlo Hhi IHhi Hb IHb
                 | G lo1 lo2 hi1 hi2 init1 init2 b1 b2 Hlo IHlo Hhi IHhi Hinit IHinit Hb IHb];
    intros H HG k1 k2 Hk; simpl.
  - (* Var *) apply Hk; [apply incl_refl | apply HG, Hin].
  - (* Num *) apply Hk; [apply incl_refl | reflexivity].
  - (* Nat *) apply Hk; [apply incl_refl | reflexivity].
  - (* Op1 *) apply IHa; auto; intros H' x1 x2 HH' Hx; simpl; split; [auto |].
    intros y1 y2; apply Hk; [intros z Hz; right; auto | left; reflexivity].
  - (* Op2 *) apply IHa; auto; intros H' x1 x2 HH' Hx.
    apply IHb; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); auto |].
    intros H'' y1 y2 HH'' Hy; simpl; split; [split; [auto | split; [apply (atom_eq_incl _ _ H'); auto | auto]] |].
    intros z1 z2; apply Hk; [intros z Hz; right; apply HH'', HH', Hz | left; reflexivity].
  - (* Get *) apply IHa; auto; intros H' x1 x2 HH' Hx.
    apply IHi; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); auto |].
    intros H'' y1 y2 HH'' Hy; simpl; split; [split; [apply (atom_eq_incl _ _ H'); auto | auto] |].
    intros z1 z2; apply Hk; [intros z Hz; right; apply HH'', HH', Hz | left; reflexivity].
  - (* Set *) apply IHa; auto; intros H' x1 x2 HH' Hx.
    apply IHi; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); auto |].
    intros H'' y1 y2 HH'' Hy.
    apply IHv; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); [intros z Hz; apply HH'', HH', Hz | auto] |].
    intros H3 w1 w2 HH3 Hw; simpl; split.
    + split; [apply (atom_eq_incl _ _ H'); [intros z Hz; apply HH3, HH'', Hz | auto] |].
      split; [apply (atom_eq_incl _ _ H''); auto | auto].
    + intros z1 z2; apply Hk; [intros z Hz; right; apply HH3, HH'', HH', Hz | left; reflexivity].
  - (* Let *) apply IHe; auto; intros H' x1 x2 HH' Hx.
    apply IHb.
    + intros u1 u2 [E | Hu]; [inversion E; subst; exact Hx | apply (atom_eq_incl _ _ H); auto].
    + intros H'' y1 y2 HH'' Hy; apply Hk; [intros z Hz; apply HH'', HH', Hz | exact Hy].
  - (* Ite *) apply IHc; auto; intros H' x1 x2 HH' Hx; simpl; split.
    + split; [exact Hx | split].
      * apply IHt; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); auto | simpl; auto].
      * apply IHe; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); auto | simpl; auto].
    + intros y1 y2; apply Hk; [intros z Hz; right; auto | left; reflexivity].
  - (* Map *) apply IHlo; auto; intros H' l1 l2 HH' Hl.
    apply IHhi; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); auto |].
    intros H'' h1 h2 HH'' Hh; simpl; split.
    + split; [apply (atom_eq_incl _ _ H'); auto | split; [exact Hh |]].
      intros i1 i2; apply (IHb (AVar i1) (AVar i2)).
      * intros u1 u2 [E | Hu]; [inversion E; subst; left; reflexivity |].
        apply (atom_eq_incl _ _ H); [intros z Hz; right; apply HH'', HH', Hz | auto].
      * simpl; auto.
    + intros y1 y2; apply Hk; [intros z Hz; right; apply HH'', HH', Hz | left; reflexivity].
  - (* Fold *) apply IHlo; auto; intros H' l1 l2 HH' Hl.
    apply IHhi; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); auto |].
    intros H'' h1 h2 HH'' Hh.
    apply IHinit; [intros u1 u2 Hu; apply (atom_eq_incl _ _ H); [intros z Hz; apply HH'', HH', Hz | auto] |].
    intros H3 x1 x2 HH3 Hx; simpl; split.
    + split; [apply (atom_eq_incl _ _ H'); [intros z Hz; apply HH3, HH'', Hz | auto] |].
      split; [apply (atom_eq_incl _ _ H''); auto | split; [exact Hx |]].
      intros i1 i2 s1 s2; apply (IHb (AVar i1) (AVar i2) (AVar s1) (AVar s2)).
      * intros u1 u2 [E | [E | Hu]]; [inversion E; subst; left; reflexivity
                                     | inversion E; subst; right; left; reflexivity |].
        apply (atom_eq_incl _ _ H); [intros z Hz; right; right; apply HH3, HH'', HH', Hz | auto].
      * simpl; auto.
    + intros y1 y2; apply Hk; [intros z Hz; right; apply HH3, HH'', HH', Hz | left; reflexivity].
Qed.

Lemma normalize_definition_eq (G : list (atom V1 * atom V2)) d1 d2 :
  definition_equiv _ _ G d1 d2 ->
  forall H, (forall a1 a2, In (a1, a2) G -> atom_eq H a1 a2) ->
  adefinition_eq H (normalize_definition d1) (normalize_definition d2).
Proof.
  induction 1 as [G n t r f1 f2 Hf IHf | G r1 r2 b1 b2 Hr Hb]; intros H HG; simpl.
  - repeat split; intros x1 x2; apply IHf.
    intros a1 a2 [E | Ha]; [inversion E; subst; left; reflexivity |].
    apply (atom_eq_incl _ _ H); [intros z Hz; right; exact Hz | auto].
  - split.
    + destruct Hr as [t | y1 y2 Hy]; simpl; [reflexivity |].
      inversion Hy; subst; simpl; auto.
    + apply (norm_eq G); auto; simpl; auto.
Qed.

End NormalizeEq.

(* The normal form of a parametric source program is parametric. *)
Theorem normalize_parametric (f : function) :
  parametric f -> forall V1 V2, adefinition_eq [] (afdef (normalize f) V1) (afdef (normalize f) V2).
Proof.
  intros Hf V1 V2; simpl.
  apply (normalize_definition_eq V1 V2 []); [apply Hf | intros a1 a2 []].
Qed.
