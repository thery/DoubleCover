(* =========================================================================  *)
(*  RowFoldOk.v -- what the folded map answers, and what a folded mark sets.  *)
(* =========================================================================  *)

(* The folded map keeps one page of each orbit under the sixteen renamings,   *)
(* and a member is read and written through the renaming that folds its page. *)
(* This file says what that is worth, in two halves.                          *)
(*                                                                            *)
(* READING: if every kept page has all twenty four bits then every member     *)
(* reads as marked, whatever page it is on.                                   *)
(*                                                                            *)
(* WRITING: a bit set by a folded mark is one that was there already, or the  *)
(* mark's own -- and the second case is exactly the two members folding to    *)
(* the same page, the same group and the same bit.                            *)
(*                                                                            *)
(* So a folded run is sound as soon as members that fold together stand or    *)
(* fall together, which is Sym16Row.sym16_row.  What is still owed is the     *)
(* level and the search, which mark and are RowRun's induction.               *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowFold.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FoldOk.

(* the three tables a member is read through: where its page is kept and by   *)
(* which renaming, the renaming on a group, the renaming on a bit             *)
Variable fpg fsgr fsbt : arr.

Notation fr pg := (fren (PArray.get fpg pg)).
Notation fp pg bt :=
  (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0%uint63 else 1%uint63)).

(* ---- reading ------------------------------------------------------------- *)

(* A FULL FOLDED MAP ANSWERS EVERY MEMBER.  The three conditions are that the *)
(* fold lands in range: a kept page, a group of that page, one of the twenty  *)
(* four bits.  They are checks on the generated tables.                       *)
Lemma mfullf_ftest m pg gr bt :
  (to_nat (fkpt (PArray.get fpg pg)) < nrepn)%N ->
  (to_nat (sgrmv fsgr (fr pg) (fp pg bt) gr) < ngroupn)%N ->
  (sbtmv fsbt (fr pg) bt <? nbiti) ->
  mfullf m -> ftest fpg fsgr fsbt m pg gr bt.
Proof.
move=> hr hg hb hm.
rewrite /ftest /fget.
have h1 := Row.iter_at hm hr.
have h2 := Row.iter_at h1 hg.
move: h2 => /eqb_spec ->.
by rewrite (allbitsP hb).
Qed.

(* ---- writing ------------------------------------------------------------- *)

(* One write is seen at one place.  A write outside an array does nothing, so *)
(* a read after a write gives what was written or what was there before, and  *)
(* that is all this needs: everything is one directional, a bit that is set   *)
(* came from somewhere.                                                       *)
Lemma fget_fset m r g v r' g' :
  fget (fset m r g v) r' g' = fget m r' g' \/
  (pchk r = pchk r' /\ Uint63.add (poff r) g = Uint63.add (poff r') g'
   /\ fget (fset m r g v) r' g' = v).
Proof.
rewrite /fget /fset.
set c := pchk r; set c' := pchk r'.
set j := Uint63.add (poff r) g; set j' := Uint63.add (poff r') g'.
set X := PArray.set (PArray.get m c) j v.
have [hc|hc] := eqVneq c c'; last first.
  by left; rewrite RowMap.get_set_otherA //; apply/eqP.
rewrite -hc.
have [hin|hin] := boolP (c <? PArray.length m)%uint63; last first.
  have hoo : (c <? PArray.length (PArray.set m c X))%uint63 = false.
    by rewrite RowMap.length_setA; apply: negbTE.
  left; rewrite (@RowMap.get_oobA _ _ hoo) RowMap.default_setA.
  by rewrite (@RowMap.get_oobA _ _ (negbTE hin)).
rewrite (@RowMap.get_setA _ _ _ hin).
have [hj|hj] := eqVneq j j'; last first.
  by left; rewrite /X get_set_otherE //; apply/eqP.
rewrite -hj.
have [hin2|hin2] := boolP (j <? PArray.length (PArray.get m c))%uint63;
    last first.
  have hoo2 : (j <? PArray.length (PArray.set (PArray.get m c) j v))%uint63
            = false.
    by rewrite RowMap.length_setE; apply: negbTE.
  by left; rewrite /X (@RowMap.get_oobE _ _ hoo2) RowMap.default_setE
                   (@RowMap.get_oobE _ _ (negbTE hin2)).
by right; split; [ | split]; rewrite // /X (@get_setE _ _ _ hin2).
Qed.

(* A BIT A FOLDED MARK SETS IS ITS OWN OR WAS THERE ALREADY, and its own      *)
(* means the two members fold to the same page, group and bit.                *)
Lemma ftest_fmark m p q c pg gr bt :
  ftest fpg fsgr fsbt (fmark fpg fsgr fsbt m p q c) pg gr bt ->
  ftest fpg fsgr fsbt m pg gr bt \/
  [/\ pchk (fkpt (PArray.get fpg p)) = pchk (fkpt (PArray.get fpg pg)),
      Uint63.add (poff (fkpt (PArray.get fpg p)))
                 (sgrmv fsgr (fr p) (fp p c) q)
      = Uint63.add (poff (fkpt (PArray.get fpg pg)))
                   (sgrmv fsgr (fr pg) (fp pg bt) gr)
    & ~~ (Uint63.land (bitof (sbtmv fsbt (fr p) c))
                      (bitof (sbtmv fsbt (fr pg) bt)) =? 0)].
Proof.
rewrite /ftest /fmark /ffor.
case: (fget_fset m (fkpt (PArray.get fpg p)) (sgrmv fsgr (fr p) (fp p c) q)
        (Uint63.lor (fget m (fkpt (PArray.get fpg p))
                       (sgrmv fsgr (fr p) (fp p c) q))
                    (bitof (sbtmv fsbt (fr p) c)))
        (fkpt (PArray.get fpg pg)) (sgrmv fsgr (fr pg) (fp pg bt) gr))
  => [->|[h1 [h2 ->]]]; first by move=> h; left.
move=> /RowMap.test_lor/orP[hin|hnew]; last by right.
left; move: hin.
have -> : fget m (fkpt (PArray.get fpg p)) (sgrmv fsgr (fr p) (fp p c) q)
        = fget m (fkpt (PArray.get fpg pg)) (sgrmv fsgr (fr pg) (fp pg bt) gr).
  by rewrite /fget h1 h2.
by [].
Qed.

(* ---- so a folded mark keeps a sound map sound ---------------------------- *)

(* P is what the map claims of a member -- for the row, that it is within the *)
(* depth.  The one thing asked of it is that members which fold together      *)
(* stand or fall together, and that is Sym16Row.sym16_row.                    *)
Variable P : int -> int -> int -> Prop.

Hypothesis Porb : forall p q c pg gr bt,
  pchk (fkpt (PArray.get fpg p)) = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff (fkpt (PArray.get fpg p)))
             (sgrmv fsgr (fr p) (fp p c) q)
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
               (sgrmv fsgr (fr pg) (fp pg bt) gr) ->
  ~~ (Uint63.land (bitof (sbtmv fsbt (fr p) c))
                  (bitof (sbtmv fsbt (fr pg) bt)) =? 0) ->
  P p q c -> P pg gr bt.

Definition soundatf (m : rmap) : Prop :=
  forall pg gr bt, ftest fpg fsgr fsbt m pg gr bt -> P pg gr bt.

Lemma soundatf_fmark m p q c :
  P p q c -> soundatf m -> soundatf (fmark fpg fsgr fsbt m p q c).
Proof.
move=> hP hm pg gr bt.
case/ftest_fmark => [h|[h1 h2 h3]]; first by apply: hm.
by apply: (Porb h1 h2 h3).
Qed.

(* ---- and a full sound map puts every member within the depth ------------- *)

Hypothesis fkptR : forall pg, (to_nat (fkpt (PArray.get fpg pg)) < nrepn)%N.
Hypothesis sgrmvR : forall pg gr bt,
  (to_nat (sgrmv fsgr (fr pg) (fp pg bt) gr) < ngroupn)%N.
Hypothesis sbtmvR : forall pg bt, (sbtmv fsbt (fr pg) bt <? nbiti).

Lemma foldf_all m : mfullf m -> soundatf m -> forall pg gr bt, P pg gr bt.
Proof.
move=> hm hs pg gr bt; apply: hs.
by apply: (mfullf_ftest (fkptR pg) (sgrmvR pg gr bt) (sbtmvR pg bt) hm).
Qed.

End FoldOk.
