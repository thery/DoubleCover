(* =========================================================================  *)
(*  RowFoldGath.v -- the gather: a renaming and then a move.                  *)
(* =========================================================================  *)

(* RowFoldConj.v says what a RENAMING does to a member, which is what the map *)
(* needs to be read at all.  The level needs one thing more: what a renaming  *)
(* AND THEN A MOVE do, because that is what one gather is.                    *)
(*                                                                            *)
(* It is kept apart from RowFoldConj because that file's sweeps are eighty    *)
(* seconds and are finished; nothing here should have to wait for them twice. *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Sym16 Moves.
Require Import Row RowMap RowFold RowMemb RowFoldPart RowTab.
Require Import RowTabF RowFoldTab RowFoldSym RowFoldConj.
Require Import RowPartC RowPartU RowPartM RowMoveH RowUp8ok RowUp4ok.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* =========================================================================  *)
(*  The folded half map, and what a bit of it came from.                      *)
(* =========================================================================  *)

(* The level moves half a word in one step: the renaming on the half, then    *)
(* the move.  RowInst.grpmvP cannot be borrowed for this -- it is about the   *)
(* plain level, which sends both halves of a word into ONE destination word,  *)
(* while the fold sends them to two different groups (measured: twoG is       *)
(* false).  So the two halves are treated one at a time here, which makes for *)
(* a smaller statement.                                                       *)

Definition clo (u k x : int) : int :=
  PArray.get mloi (Uint63.add (Uint63.lsl k 12)
                     (PArray.get fsloi (Uint63.add (Uint63.lsl u 12) x))).
Definition chi (u k x : int) : int :=
  PArray.get mhii (Uint63.add (Uint63.lsl k 12)
                     (PArray.get fshii (Uint63.add (Uint63.lsl u 12) x))).

(* ONE BIT GOES TO ONE BIT: the image of a single bit is a power of two,      *)
(* nonzero, and inside the twelve.                                            *)
Definition c1C : bool :=
  iter nsymn 0%uint63 (fun u => iter nhn 0%uint63 (fun k =>
    iter nlon 0%uint63 (fun i =>
      let a := clo u k (Uint63.lsl 1 i) in
      let b := chi u k (Uint63.lsl 1 i) in
      [&& (a <? nhalfi)%uint63, (Uint63.land a (Uint63.sub a 1) =? 0)%uint63,
          negb (a =? 0)%uint63, (b <? nhalfi)%uint63,
          (Uint63.land b (Uint63.sub b 1) =? 0)%uint63 &
          negb (b =? 0)%uint63]))).
Lemma c1CP : c1C. Proof. by vm_compute. Qed.

(* ---- and it is additive over the twelve bits ----------------------------- *)

(* THE SUM IS WRITTEN OUT, NOT FOLDED.  Everything the fold does is int63 and *)
(* so is this: twelve conditional words ored together, no list and no nat in  *)
(* sight.                                                                     *)
Definition cbit (f : int -> int -> int -> int) (u k x i : int) : int :=
  if (Uint63.land (Uint63.lsr x i) 1 =? 0)%uint63 then 0%uint63
  else f u k (Uint63.lsl 1 i).

Definition cadd (f : int -> int -> int -> int) (u k x : int) : int :=
  Uint63.lor (Uint63.lor (Uint63.lor (Uint63.lor
   (Uint63.lor (Uint63.lor (Uint63.lor (Uint63.lor
    (Uint63.lor (Uint63.lor (Uint63.lor
     (cbit f u k x 0) (cbit f u k x 1)) (cbit f u k x 2)) (cbit f u k x 3))
      (cbit f u k x 4)) (cbit f u k x 5)) (cbit f u k x 6)) (cbit f u k x 7))
       (cbit f u k x 8)) (cbit f u k x 9)) (cbit f u k x 10))
        (cbit f u k x 11).

Definition caddok (u k x : int) : bool :=
  (clo u k x =? cadd clo u k x)%uint63 && (chi u k x =? cadd chi u k x)%uint63.

Definition caddC : bool :=
  iter nsymn 0%uint63 (fun u => iter nhn 0%uint63 (fun k =>
    iter nhalfn 0%uint63 (caddok u k))).
Lemma caddCP : caddC. Proof. by vm_compute. Qed.

(* THE SWEEP RESTATED, AND IT IS NOT DECORATION.  Reading one word out of the *)
(* check by iter_at directly makes the unifier unfold the check itself, and   *)
(* the Qed of the lemma below took 256 SECONDS that way.  Handed the same     *)
(* fact through this equation -- which is reflexivity, checked once -- it is  *)
(* 28 milliseconds.  RowInst does the same with halfokE and srcokE.           *)
Lemma caddCE : caddC =
  iter nsymn 0%uint63 (fun u => iter nhn 0%uint63 (fun k =>
    iter nhalfn 0%uint63 (caddok u k))).
Proof. by []. Qed.

(* ---- so a bit of a moved half came from a bit of the half ---------------- *)

Lemma cbit_bit f u k x i j :
  ~~ (Uint63.land (cbit f u k x i) (bitof j) =? 0)%uint63 ->
  (Uint63.land (Uint63.lsr x i) 1 =? 0)%uint63 = false /\
  ~~ (Uint63.land (f u k (Uint63.lsl 1 i)) (bitof j) =? 0)%uint63.
Proof.
rewrite /cbit; case: ifP => h.
  by rewrite RowMap.land0n Uint63.eqb_refl.
by move=> hp; split.
Qed.

Lemma cadd_bit f u k x j :
  ~~ (Uint63.land (cadd f u k x) (bitof j) =? 0)%uint63 ->
  exists2 i, (i <? 12)%uint63 &
    (Uint63.land (Uint63.lsr x i) 1 =? 0)%uint63 = false /\
    ~~ (Uint63.land (f u k (Uint63.lsl 1 i)) (bitof j) =? 0)%uint63.
Proof.
rewrite /cadd => h.
case/RowMap.test_lor/orP: h => h; last by exists 11 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 10 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 9 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 8 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 7 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 6 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 5 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 4 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 3 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 2 => //; exact: cbit_bit h.
case/RowMap.test_lor/orP: h => h; last by exists 1 => //; exact: cbit_bit h.
by exists 0 => //; exact: cbit_bit h.
Qed.

Lemma clo_bit u k x j : (to_nat u < nsymn)%N -> (to_nat k < nhn)%N ->
  (to_nat x < nhalfn)%N ->
  ~~ (Uint63.land (clo u k x) (bitof j) =? 0)%uint63 ->
  exists2 i, (i <? 12)%uint63 &
    (Uint63.land (Uint63.lsr x i) 1 =? 0)%uint63 = false /\
    ~~ (Uint63.land (clo u k (Uint63.lsl 1 i)) (bitof j) =? 0)%uint63.
Proof.
move=> hu hk hx.
have h1 := caddCP; rewrite caddCE in h1.
have /andP[/eqP e _] := Row.iter_at (Row.iter_at (Row.iter_at h1 hu) hk) hx.
by rewrite e; apply: cadd_bit.
Qed.

Lemma chi_bit u k x j : (to_nat u < nsymn)%N -> (to_nat k < nhn)%N ->
  (to_nat x < nhalfn)%N ->
  ~~ (Uint63.land (chi u k x) (bitof j) =? 0)%uint63 ->
  exists2 i, (i <? 12)%uint63 &
    (Uint63.land (Uint63.lsr x i) 1 =? 0)%uint63 = false /\
    ~~ (Uint63.land (chi u k (Uint63.lsl 1 i)) (bitof j) =? 0)%uint63.
Proof.
move=> hu hk hx.
have h1 := caddCP; rewrite caddCE in h1.
have /andP[_ /eqP e] := Row.iter_at (Row.iter_at (Row.iter_at h1 hu) hk) hx.
by rewrite e; apply: cadd_bit.
Qed.

(* =========================================================================  *)
(*  A bit of the source is a member, with no renaming in the way.             *)
(* =========================================================================  *)

(* To read a source bit as a member, a member has to be exhibited that folds  *)
(* there.  The kept page itself is the one: it is its own representative, and *)
(* the renaming it names leaves groups and bits alone.  Twenty three seconds  *)
(* to check, and it is what lets the level's source word be read as members   *)
(* the source map already claims.                                             *)
Definition keepidC : bool :=
  iter nrepn 0%uint63 (fun r =>
    let pg := PArray.get fkeepi r in
    let w := PArray.get fpgi pg in
    (fkpt w =? r)%uint63 &&
    (iter ngroupn 0%uint63 (fun g =>
       iter nptyn 0%uint63 (fun pty =>
         (sgrmv fsgri (fren w) pty g =? g)%uint63)) &&
     iter nbitn 0%uint63 (fun bt => (sbtmv fsbti (fren w) bt =? bt)%uint63))).
Lemma keepidCP : keepidC. Proof. by vm_compute. Qed.

(* read through an equation, never straight -- see caddCE *)
Lemma keepidCE : keepidC =
  iter nrepn 0%uint63 (fun r =>
    let pg := PArray.get fkeepi r in
    let w := PArray.get fpgi pg in
    (fkpt w =? r)%uint63 &&
    (iter ngroupn 0%uint63 (fun g =>
       iter nptyn 0%uint63 (fun pty =>
         (sgrmv fsgri (fren w) pty g =? g)%uint63)) &&
     iter nbitn 0%uint63 (fun bt => (sbtmv fsbti (fren w) bt =? bt)%uint63))).
Proof. by []. Qed.

Lemma keepid r : (to_nat r < nrepn)%N ->
  let w := PArray.get fpgi (PArray.get fkeepi r) in
  [/\ fkpt w = r,
      forall g pty, (to_nat g < ngroupn)%N -> (to_nat pty < nptyn)%N ->
        sgrmv fsgri (fren w) pty g = g
    & forall bt, (to_nat bt < nbitn)%N -> sbtmv fsbti (fren w) bt = bt].
Proof.
move=> hr; have h1 := keepidCP; rewrite keepidCE in h1.
have h2 := Row.iter_at h1 hr; cbv zeta in h2.
have /andP[/eqP e1 /andP[e2 e3]] := h2.
split=> // [g pty hg hp|bt hb].
  by apply/eqP; exact: (Row.iter_at (Row.iter_at e2 hg) hp).
by apply/eqP; exact: (Row.iter_at e3 hb).
Qed.

(* SO THE FOLDED MAP READ AT A KEPT SLOT IS THE SLOT ITSELF.  A bit of the   *)
(* source word the level reads is a member the source map claims, with no    *)
(* renaming to undo.                                                         *)
Lemma keep_ftest src r g bt : (to_nat r < nrepn)%N -> (to_nat g < ngroupn)%N ->
  (to_nat bt < nbitn)%N ->
  ftest fpgi fsgri fsbti src (PArray.get fkeepi r) g bt
  = ~~ (Uint63.land (fget src r g) (bitof bt) =? 0)%uint63.
Proof.
move=> hr hg hb.
have hpg : (to_nat (PArray.get fkeepi r) < npagen)%N.
  by apply/nltbP; apply: (Row.iter_at keepRCP hr).
have hp : (to_nat (Ptyof (PArray.get fkeepi r) bt) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP hpg) hb).
have := keepid hr; cbv zeta => -[e1 e2 e3].
by rewrite /ftest e1 (e2 _ _ hg hp) (e3 _ hb).
Qed.
