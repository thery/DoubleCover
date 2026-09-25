(* =========================================================================  *)
(*  RowSrchSim.v -- the plain int run does not see how a position is kept.    *)
(* =========================================================================  *)

(* RowFoldSim's lemma, for the plain map.  runskic moves a position and reads *)
(* a member off it, and does nothing else with it.  Two kinds of position     *)
(* that move in step, and give the same member wherever the search reads one, *)
(* give the same map.                                                         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask RowSrch RowSrchP RowSrchC.
Require Import RowFoldSim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section SSim.

Variable e8num e4bit : arr.
Variable prep : rmap -> rmap -> rmap.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Variable cstep : int -> int -> int.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.
Variable croot : int.
Variable dsrch : nat.
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

Local Notation srki1 :=
  (RowSrch.srchki e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation srki2 :=
  (RowSrch.srchki e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation srski1 :=
  (RowSrch.srchski e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation srski2 :=
  (RowSrch.srchski e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation srkiL1 :=
  (srchkiL e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation srkiL2 :=
  (srchkiL e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation srskiL1 :=
  (srchskiL e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation srskiL2 :=
  (srchskiL e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation slv1 :=
  (slvlski e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch ishm).
Local Notation slv2 :=
  (slvlski e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch ishm).
Local Notation run1 :=
  (runskic e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch ishm).
Local Notation run2 :=
  (runskic e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch ishm).

(* ---- the searches ---------------------------------------------------------- *)

Lemma srchki_sim cut togo :
  forall togoi c x1 x2 msk pv m, R c x1 x2 ->
  srki1 cut togo togoi c x1 msk pv m = srki2 cut togo togoi c x2 msk pv m.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv m hR.
  by rewrite /=; case: ifP => hs //; rewrite (R_leaf hR hs).
rewrite /RowSrch.srchki.
cbv zeta.
apply: ifold_eqi; first exact: nmvn_nwB.
move=> k m' hk.
do 3 apply: if_else.
apply: if_then => _.
by apply: ih; apply: R_step.
Qed.

Lemma srchski_sim cut togo :
  forall togoi c x1 x2 msk pv enough mn, R c x1 x2 ->
  srski1 cut togo togoi c x1 msk pv enough mn
  = srski2 cut togo togoi c x2 msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv enough mn hR.
  rewrite /=; case: (Uint63.leb enough mn.2); first by [].
  by case: ifP => hs //; rewrite (R_leaf hR hs).
rewrite /RowSrch.srchski.
case: (Uint63.leb enough mn.2); first by [].
cbv zeta.
apply: ifold_eqi; first exact: nmvn_nwB.
move=> k a hk.
do 3 apply: if_else.
apply: if_then => _.
by apply: ih; apply: R_step.
Qed.

Lemma srchkiL_sim cut togo :
  forall togoi c x1 x2 msk pv m, R c x1 x2 ->
  srkiL1 cut togo togoi c x1 msk pv m = srkiL2 cut togo togoi c x2 msk pv m.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv m hR.
  by apply: srchki_sim.
case: togo ih => [|togo] ih.
  rewrite /srchkiL.
  apply: ifold_eqi; first exact: nmvn_nwB.
  move=> k m' hk.
  do 3 apply: if_else.
  by apply: srchki_sim; apply: R_step.
rewrite /srchkiL.
cbv zeta.
apply: ifold_eqi; first exact: nmvn_nwB.
move=> k m' hk.
do 3 apply: if_else.
apply: if_then => _.
by apply: ih; apply: R_step.
Qed.

Lemma srchskiL_sim cut togo :
  forall togoi c x1 x2 msk pv enough mn, R c x1 x2 ->
  srskiL1 cut togo togoi c x1 msk pv enough mn
  = srskiL2 cut togo togoi c x2 msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv enough mn hR.
  rewrite /srchskiL; case: (Uint63.leb enough mn.2); first by [].
  by apply: srchski_sim.
rewrite /srchskiL.
case: (Uint63.leb enough mn.2); first by [].
case: togo ih => [|togo] ih.
  apply: ifold_eqi; first exact: nmvn_nwB.
  move=> k a hk.
  do 3 apply: if_else.
  by apply: srchski_sim; apply: R_step.
cbv zeta.
apply: ifold_eqi; first exact: nmvn_nwB.
move=> k a hk.
do 3 apply: if_else.
apply: if_then => _.
by apply: ih; apply: R_step.
Qed.

(* ---- the level and the run -------------------------------------------------- *)

Lemma slvlski_sim cut d m : slv1 cut d m = slv2 cut d m.
Proof.
rewrite /slvlski; cbv zeta.
case: ifP => _ //; case: ifP => _ //; case: ifP => _.
  by apply: (f_equal fst); apply: srchskiL_sim; exact: R_root.
by apply: srchkiL_sim; exact: R_root.
Qed.

Lemma runskic_sim n d n0 m dst : run1 n d n0 m dst = run2 n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst; first by [].
rewrite /runskic; cbv zeta.
case: (Uint63.ltb ncutb n0); rewrite !slvlski_sim; exact: ih.
Qed.

End SSim.
