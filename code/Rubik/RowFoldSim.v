(* =========================================================================  *)
(*  RowFoldSim.v -- the folded int run does not see how a position is kept.   *)
(* =========================================================================  *)

(* frunskic moves a position and reads a member off it, and does nothing      *)
(* else with it.  Two kinds of position that move in step, and give the same  *)
(* member wherever the search reads one, give the same map.  This is what     *)
(* lets the run carry hcoset's four numbers while the proof is RowFoldRunC's  *)
(* over the twenty cubies.                                                    *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask.
Require Import RowFold RowFoldSrch RowFoldSrchI RowFoldSrchIP RowFoldRunC.
Require Import RowFoldSrchIC RowLeafFast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- two folds that agree on the numbers they reach ----------------------- *)

Lemma ifold_eqg (A : Type) n j (f g : int -> A -> A) a :
  (j + n <= nwB)%N ->
  (forall k b, (to_nat k < j + n)%N -> f k b = g k b) ->
  ifold n (advn j 0%uint63) f a = ifold n (advn j 0%uint63) g a.
Proof.
elim: n j a => [|n ih] j a hb hfg //=.
have -> : Uint63.add (advn j 0%uint63) 1%uint63 = advn j.+1 0%uint63.
  by rewrite advnS.
have hk : (to_nat (advn j 0%uint63) < j + n.+1)%N.
  rewrite to_nat_advn0; first by rewrite addnS ltnS leq_addr.
  by apply: leq_trans hb; rewrite addnS ltnS leq_addr.
rewrite (hfg _ _ hk); apply: ih; first by rewrite addSnnS.
by move=> k b hk'; apply: hfg; rewrite -addSnnS.
Qed.

Lemma ifold_eqi (A : Type) n (f g : int -> A -> A) a :
  (n <= nwB)%N ->
  (forall k b, (to_nat k < n)%N -> f k b = g k b) ->
  ifold n 0%uint63 f a = ifold n 0%uint63 g a.
Proof. by move=> hb hfg; apply: (@ifold_eqg _ n 0). Qed.

Lemma nmvn_nwB : (RowRun.nmvn <= nwB)%N.
Proof. by apply: ltnW; apply: (@lt_nwB _ 5). Qed.

(* two ifs on the same test, compared branch by branch: a bare `by []` would *)
(* unify the two branches side by side, and those are two whole searches     *)
Lemma if_else (A : Type) (b : bool) (a x y : A) :
  x = y -> (if b then a else x) = (if b then a else y).
Proof. by move=> ->. Qed.
Lemma if_then (A : Type) (b : bool) (x y z : A) :
  (b -> x = y) -> (if b then x else z) = (if b then y else z).
Proof. by case: b => // ->. Qed.

Section FSim.

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Variable cstep : int -> int -> int.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.
Variable croot : int.
Variable dsrch : nat.
Variables forb fpop : arr.
Variable ishm : int.

(* ---- the two kinds of position -------------------------------------------- *)

Variables pst1 pst2 : Type.
Variable xstep1 : pst1 -> int -> pst1.
Variable xstep2 : pst2 -> int -> pst2.
Variable tomemb1 : pst1 -> memb.
Variable tomemb2 : pst2 -> memb.
Variable sroot1 : pst1.
Variable sroot2 : pst2.

(* in step, beside the phase one coordinate *)
Variable R : int -> pst1 -> pst2 -> Prop.

Hypothesis R_root : R croot sroot1 sroot2.
Hypothesis R_step : forall c x1 x2 k, (to_nat k < RowRun.nmvn)%N ->
  R c x1 x2 -> R (cstep c k) (xstep1 x1 k) (xstep2 x2 k).
Hypothesis R_leaf : forall c x1 x2, R c x1 x2 -> csolved c ->
  tomemb1 x1 = tomemb2 x2.

Local Notation fsrki1 :=
  (fsrchki e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation fsrki2 :=
  (fsrchki e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation fsrski1 :=
  (fsrchski e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation fsrski2 :=
  (fsrchski e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation isrkL1 :=
  (isrchkL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation isrkL2 :=
  (isrchkL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation isrskL1 :=
  (isrchskL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation isrskL2 :=
  (isrchskL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation frun1 :=
  (frunskic e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch forb fpop ishm).
Local Notation frun2 :=
  (frunskic e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch forb fpop ishm).

(* ---- the searches ---------------------------------------------------------- *)

Lemma fsrchki_sim cut togo :
  forall togoi c x1 x2 msk pv m, R c x1 x2 ->
  fsrki1 cut togo togoi c x1 msk pv m = fsrki2 cut togo togoi c x2 msk pv m.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv m hR.
  by rewrite /=; case: ifP => hs //; rewrite (R_leaf hR hs).
rewrite /fsrchki.
cbv zeta.
apply: ifold_eqi.
  exact: nmvn_nwB.
move=> k m' hk.
case: ifP => _; first by [].
case: ifP => _; first by [].
case: ifP => _; first by [].
case: ifP => _; last by [].
apply: ih.
by apply: R_step.
Qed.

Lemma fsrchski_sim cut togo :
  forall togoi c x1 x2 msk pv enough mn, R c x1 x2 ->
  fsrski1 cut togo togoi c x1 msk pv enough mn
  = fsrski2 cut togo togoi c x2 msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv enough mn hR.
  rewrite /=; case: (Uint63.leb enough mn.2); first by [].
  by case: ifP => hs //; rewrite (R_leaf hR hs).
rewrite /fsrchski.
case: (Uint63.leb enough mn.2); first by [].
cbv zeta.
apply: ifold_eqi; first exact: nmvn_nwB.
move=> k a hk.
case: ifP => _; first by [].
case: ifP => _; first by [].
case: ifP => _; first by [].
case: ifP => _; last by [].
apply: ih.
by apply: R_step.
Qed.

Lemma isrchkL_sim cut togo :
  forall togoi c x1 x2 msk pv m, R c x1 x2 ->
  isrkL1 cut togo togoi c x1 msk pv m = isrkL2 cut togo togoi c x2 msk pv m.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv m hR.
  by apply: fsrchki_sim.
case: togo ih => [|togo] ih.
  rewrite /isrchkL.
  apply: ifold_eqi; first exact: nmvn_nwB.
  move=> k m' hk.
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  by apply: fsrchki_sim; apply: R_step.
rewrite /isrchkL.
cbv zeta.
apply: ifold_eqi; first exact: nmvn_nwB.
move=> k m' hk.
do 3 apply: if_else.
apply: if_then => _.
by apply: ih; apply: R_step.
Qed.

Lemma isrchskL_sim cut togo :
  forall togoi c x1 x2 msk pv enough mn, R c x1 x2 ->
  isrskL1 cut togo togoi c x1 msk pv enough mn
  = isrskL2 cut togo togoi c x2 msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv enough mn hR.
  rewrite /isrchskL; case: (Uint63.leb enough mn.2); first by [].
  by apply: fsrchski_sim.
rewrite /isrchskL.
case: (Uint63.leb enough mn.2); first by [].
case: togo ih => [|togo] ih.
  apply: ifold_eqi; first exact: nmvn_nwB.
  move=> k a hk.
  do 3 apply: if_else.
  by apply: fsrchski_sim; apply: R_step.
cbv zeta.
apply: ifold_eqi; first exact: nmvn_nwB.
move=> k a hk.
do 3 apply: if_else.
apply: if_then => _.
by apply: ih; apply: R_step.
Qed.

(* ---- the level and the run -------------------------------------------------- *)

Lemma frunskic_sim n d n0 m dst : frun1 n d n0 m dst = frun2 n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst; first by [].
have hl : forall cut d' m',
  fslvski e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
    cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch forb fpop ishm
    cut d' m'
  = fslvski e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
    cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch forb fpop ishm
    cut d' m'.
  move=> cut d' m'; rewrite /fslvski; cbv zeta.
  case: ifP => _ //; case: ifP => _ //; case: ifP => _.
    by apply: (f_equal fst); apply: isrchskL_sim; exact: R_root.
  by apply: isrchkL_sim; exact: R_root.
rewrite /frunskic; cbv zeta.
case: (Uint63.ltb ncutb n0); rewrite !hl; exact: ih.
Qed.

End FSim.
