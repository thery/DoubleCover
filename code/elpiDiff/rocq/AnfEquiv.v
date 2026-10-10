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
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

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
Proof.
by case: a1 => [x1 | s1 | k1]; case: a2 => [x2 | s2 | k2] //= /(_ (x1, x2)).
Qed.

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
elim=> {G t1 t2} [G x1 x2 Hin | G s | G n | G f a1 a2 Ha IHa
  | G f a1 a2 b1 b2 Ha IHa Hb IHb | G a1 a2 i1 i2 Ha IHa Hi IHi
  | G a1 a2 i1 i2 v1 v2 Ha IHa Hi IHi Hv IHv
  | G e1 e2 b1 b2 He IHe Hb IHb
  | G c1 c2 t1 t2 e1 e2 Hc IHc Ht IHt He IHe
  | G lo1 lo2 hi1 hi2 b1 b2 Hlo IHlo Hhi IHhi Hb IHb
  | G lo1 lo2 hi1 hi2 init1 init2 b1 b2 Hlo IHlo Hhi IHhi Hinit IHinit Hb IHb]
  H HG k1 k2 Hk /=.
- (* Var *) by apply: Hk (incl_refl _) (HG _ _ Hin).
- (* Num *) by apply: Hk (incl_refl _) _.
- (* Nat *) by apply: Hk (incl_refl _) _.
- (* Op1 *) apply: IHa => // H' x1 x2 HH' Hx /=; split=> // y1 y2.
  apply: Hk; last by left.
  by move=> z Hz; right; apply: HH'.
- (* Op2 *) apply: IHa => // H' x1 x2 HH' Hx.
  apply: IHb => [u1 u2 Hu | H'' y1 y2 HH'' Hy /=].
    by apply: (atom_eq_incl _ _ H) HH' _; apply: HG.
  split.
    by split=> //; split=> //; apply: (atom_eq_incl _ _ H') HH'' Hx.
  move=> z1 z2; apply: Hk; last by left.
  by move=> z Hz; right; apply/HH''/HH'.
- (* Get *) apply: IHa => // H' x1 x2 HH' Hx.
  apply: IHi => [u1 u2 Hu | H'' y1 y2 HH'' Hy /=].
    by apply: (atom_eq_incl _ _ H) HH' _; apply: HG.
  split; first by split=> //; apply: (atom_eq_incl _ _ H') HH'' Hx.
  move=> z1 z2; apply: Hk; last by left.
  by move=> z Hz; right; apply/HH''/HH'.
- (* Set *) apply: IHa => // H' x1 x2 HH' Hx.
  apply: IHi => [u1 u2 Hu | H'' y1 y2 HH'' Hy].
    by apply: (atom_eq_incl _ _ H) HH' _; apply: HG.
  apply: IHv => [u1 u2 Hu | H3 w1 w2 HH3 Hw /=].
    apply: (atom_eq_incl _ _ H); last exact: HG.
    by move=> z Hz; apply/HH''/HH'.
  split.
    split; first by apply: (atom_eq_incl _ _ H') Hx => z Hz; apply/HH3/HH''.
    by split=> //; apply: (atom_eq_incl _ _ H'') HH3 Hy.
  move=> z1 z2; apply: Hk; last by left.
  by move=> z Hz; right; apply/HH3/HH''/HH'.
- (* Let *) apply: IHe => // H' x1 x2 HH' Hx.
  apply: IHb => [u1 u2 [E | Hu] | H'' y1 y2 HH'' Hy].
  - by case: E => <- <-.
  - by apply: (atom_eq_incl _ _ H) HH' _; apply: HG.
  by apply: Hk => // z Hz; apply/HH''/HH'.
- (* Ite *) apply: IHc => // H' x1 x2 HH' Hx /=; split.
    split=> //; split.
      apply: IHt => [u1 u2 Hu | //].
      by apply: (atom_eq_incl _ _ H) HH' _; apply: HG.
    apply: IHe => [u1 u2 Hu | //].
    by apply: (atom_eq_incl _ _ H) HH' _; apply: HG.
  move=> y1 y2; apply: Hk; last by left.
  by move=> z Hz; right; apply: HH'.
- (* Map *) apply: IHlo => // H' l1 l2 HH' Hl.
  apply: IHhi => [u1 u2 Hu | H'' h1 h2 HH'' Hh /=].
    by apply: (atom_eq_incl _ _ H) HH' _; apply: HG.
  split.
    split; first exact: (atom_eq_incl _ _ H') HH'' Hl.
    split=> // i1 i2.
    apply: (IHb (AVar i1) (AVar i2)) => [u1 u2 [[<- <-] | Hu] | //].
      by left.
    apply: (atom_eq_incl _ _ H); last exact: HG.
    by move=> z Hz; right; apply/HH''/HH'.
  move=> y1 y2; apply: Hk; last by left.
  by move=> z Hz; right; apply/HH''/HH'.
(* Fold *)
apply: IHlo => // H' l1 l2 HH' Hl.
apply: IHhi => [u1 u2 Hu | H'' h1 h2 HH'' Hh].
  by apply: (atom_eq_incl _ _ H) HH' _; apply: HG.
apply: IHinit => [u1 u2 Hu | H3 x1 x2 HH3 Hx /=].
  apply: (atom_eq_incl _ _ H); last exact: HG.
  by move=> z Hz; apply/HH''/HH'.
split.
  split; first by apply: (atom_eq_incl _ _ H') Hl => z Hz; apply/HH3/HH''.
  split; first exact: (atom_eq_incl _ _ H'') HH3 Hh.
  split=> // i1 i2 s1 s2.
  apply: (IHb (AVar i1) (AVar i2) (AVar s1) (AVar s2))
    => [u1 u2 [[<- <-] | [[<- <-] | Hu]] | //].
  - by left.
  - by right; left.
  apply: (atom_eq_incl _ _ H); last exact: HG.
  by move=> z Hz; right; right; apply/HH3/HH''/HH'.
move=> y1 y2; apply: Hk; last by left.
by move=> z Hz; right; apply/HH3/HH''/HH'.
Qed.

Lemma normalize_definition_eq (G : list (atom V1 * atom V2)) d1 d2 :
  definition_equiv _ _ G d1 d2 ->
  forall H, (forall a1 a2, In (a1, a2) G -> atom_eq H a1 a2) ->
  adefinition_eq H (normalize_definition d1) (normalize_definition d2).
Proof.
elim=> {G d1 d2} [G n t r f1 f2 Hf IHf | G r1 r2 b1 b2 Hr Hb] H HG /=.
  do 3!split=> //; move=> x1 x2; apply: IHf => a1 a2 [[<- <-] | Ha].
    by left.
  apply: (atom_eq_incl _ _ H); last exact: HG.
  by move=> z Hz; right.
split; last by apply: (norm_eq G) => // H' a1 a2.
by case: Hr => [t | y1 y2 Hy] //=; case: Hy => /=; auto.
Qed.

End NormalizeEq.

(* The normal form of a parametric source program is parametric. *)
Theorem normalize_parametric (f : function) :
  parametric f -> forall V1 V2, adefinition_eq [] (afdef (normalize f) V1) (afdef (normalize f) V2).
Proof.
move=> Hf V1 V2 /=.
by apply: (normalize_definition_eq V1 V2 []) => // a1 a2 [].
Qed.
