(* =========================================================================  *)
(*  RowFoldMem.v -- two members that fold together stand or fall together.    *)
(* =========================================================================  *)

(* RowFoldOk asks one thing of what the map claims: that members which fold   *)
(* to the same page, the same group and the same bit stand or fall together.  *)
(* That is Porb, and it is the only place the fold needs the cube at all.     *)
(*                                                                            *)
(* It comes in two halves.  FOLDING TO THE SAME PLACE IS BEING THE SAME       *)
(* PLACE: the chunk and the offset inside it determine the kept page and the  *)
(* group, and two of the twenty four bits meet only when they are the same    *)
(* bit.  That half is arithmetic and is proved here.                          *)
(*                                                                            *)
(* AND THE PLACE IS THE MEMBER RENAMED.  Two members that land there are      *)
(* therefore each other's image under one of the sixteen, and Sym16Row's      *)
(* sym16_ball says the ball does not notice.  That half is the hypothesis     *)
(* below, and it is what the fold still owes.                                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Sym16 Sym16Row.
Require Import Moves Row RowMap RowFold RowFoldOk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- a chunk and an offset name one kept page and one group -------------- *)

(* The fold finds a word by a shift and a mask, as RowMap does, and those two *)
(* are the quotient and the remainder by the sixty four pages a chunk holds.  *)
Lemma pchkE r : pchk r = Uint63.div r 64.
Proof.
rewrite /pchk; have -> : (64 = Uint63.lsl one ppcshft)%uint63 by vm_compute.
by apply: div_one_lsl_lsr.
Qed.

Lemma pmskE r : Uint63.land r ppcmask = Uint63.mod r 64.
Proof.
have -> : ppcmask = decr (Uint63.lsl one ppcshft) by vm_compute.
have -> : (64 = Uint63.lsl one ppcshft)%uint63 by vm_compute.
by apply: land_power2.
Qed.

(* the page inside a chunk is under sixty four, so it is certainly a page *)
Lemma pmsk_page r : (Uint63.land r ppcmask <? npagei)%uint63.
Proof.
apply/nltbP; rewrite pmskE to_nat_mod.
apply: leq_trans (_ : 64 <= npagen)%N; last by rewrite npagenE.
by apply: ltn_pmod.
Qed.

(* SO FOLDING TO THE SAME PLACE IS BEING THE SAME PLACE.  The offset a page   *)
(* starts at plus a group is exactly RowMap's grpof of the page inside the    *)
(* chunk, so the same argument settles it.                                    *)
Lemma fslot_inj r G r' G' :
  (G <? ngroupi)%uint63 -> (G' <? ngroupi)%uint63 ->
  pchk r = pchk r' -> Uint63.add (poff r) G = Uint63.add (poff r') G' ->
  r = r' /\ G = G'.
Proof.
move=> hG hG' hc he.
have hE : forall x g, Uint63.add (poff x) g = grpof (Uint63.land x ppcmask) g
  by [].
rewrite !hE in he.
have [hp hg] := grpof_inj (pmsk_page r) hG (pmsk_page r') hG' he.
split=> //.
(* THE DIVISION, NEVER THE BITS, and never a nat: int_add_mod puts a number  *)
(* back together from its quotient and its remainder, and going through      *)
(* to_nat here does not come back.                                          *)
by rewrite {1}(int_add_mod r 64) {1}(int_add_mod r' 64) -!pchkE hc -!pmskE hp.
Qed.

(* ---- so two members that fold together fold to the same place ------------ *)

Section Same.

Variable fpg fsgr fsbt : arr.

Notation fr pg := (fren (PArray.get fpg pg)).
Notation fp pg bt :=
  (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0%uint63 else 1%uint63)).

(* the two ranges RowFoldOk asks of the tables, and RowFoldChkTab checks *)
Hypothesis sgrmvR : forall pg gr bt,
  (to_nat (sgrmv fsgr (fr pg) (fp pg bt) gr) < ngroupn)%N.
Hypothesis sbtmvR : forall pg bt, (sbtmv fsbt (fr pg) bt <? nbiti).

(* THE ARITHMETIC HALF OF Porb.  Its three premises are a chunk, an offset    *)
(* and a bit that meet; this says they name one kept page, one group and one  *)
(* bit.  What is then owed is that the place is the member renamed, and that  *)
(* is the half the fold still has to prove.                                   *)
Lemma forb_same p q c pg gr bt :
  pchk (fkpt (PArray.get fpg p)) = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff (fkpt (PArray.get fpg p))) (sgrmv fsgr (fr p) (fp p c) q)
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
               (sgrmv fsgr (fr pg) (fp pg bt) gr) ->
  ~~ (Uint63.land (bitof (sbtmv fsbt (fr p) c))
                  (bitof (sbtmv fsbt (fr pg) bt)) =? 0) ->
  [/\ fkpt (PArray.get fpg p) = fkpt (PArray.get fpg pg),
      sgrmv fsgr (fr p) (fp p c) q = sgrmv fsgr (fr pg) (fp pg bt) gr &
      sbtmv fsbt (fr p) c = sbtmv fsbt (fr pg) bt].
Proof.
move=> hc hg hb.
have h1 : (sgrmv fsgr (fr p) (fp p c) q <? ngroupi)%uint63.
  by apply/nltbP; apply: sgrmvR.
have h2 : (sgrmv fsgr (fr pg) (fp pg bt) gr <? ngroupi)%uint63.
  by apply/nltbP; apply: sgrmvR.
have [he1 he2] := fslot_inj h1 h2 hc hg.
by split=> //; apply: bitof_inj hb.
Qed.

End Same.
