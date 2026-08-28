(* =========================================================================  *)
(*  RowFoldLvl.v -- the folded level keeps a map sound.                       *)
(* =========================================================================  *)

(* RowRun.prepass_sound says a bit the plain level writes is a member one     *)
(* move of H further out than a bit the source had.  This is the same for the *)
(* folded level, with two differences.                                        *)
(*                                                                            *)
(* IT FILLS A PAGE ARRAY, NOT THE MAP.  Every write of a kept page is made    *)
(* into one array and the chunk is put back once at the end.  RowFoldOk's     *)
(* ffor_setp turns that array write into the map write it stands for, so the  *)
(* induction runs with "the map with this chunk put back is sound".           *)
(*                                                                            *)
(* AND IT GATHERS THROUGH A RENAMING.  The word it reads is not the one the   *)
(* plain level would read but its image under one of the sixteen, so what is  *)
(* owed at each write is a member one move out from a member of the RENAMED   *)
(* source -- and Sym16Row.sym16_row is what says the renaming costs nothing.  *)
(*                                                                            *)
(* The two facts about the gathered word are hypotheses here, in the shape    *)
(* RowRun.v uses for grpmvP and prep_move: the algorithm is proved and what   *)
(* the tables mean is left to the instance, which RowFoldSym.v now checks.    *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowFold RowFoldOk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- putting a chunk back where it came from ----------------------------- *)

(* The level reads a chunk, fills it and puts it back.  When it has written   *)
(* nothing the map is the one it started from, and that is what lets the      *)
(* carry and the ten moves be argued about one write at a time.               *)
Lemma set_getA (t : rmap) i :
  (i <? PArray.length t) -> PArray.set t i (PArray.get t i) = t.
Proof.
move=> hin; apply: array_ext.
- by rewrite RowMap.length_setA.
- move=> j hj.
  have [hij|hij] := eqVneq i j.
    by rewrite -hij RowMap.get_setA //; move: hj; rewrite RowMap.length_setA hij.
  by rewrite RowMap.get_set_otherA //; apply/eqP.
by rewrite RowMap.default_setA.
Qed.

Section FoldLvl.

(* the six tables a member is read and gathered through *)
Variable fpg fsrc fsgr fslo fshi fsbt : arr.

(* and the move, on groups, halves and bits *)
Variable mgr msw mlo mhi : arr.

Notation lvmv := (flevmv fsrc fsgr fslo fshi mgr msw mlo mhi).
Notation lvpg := (flevpg fsrc fsgr fslo fshi mgr msw mlo mhi).
Notation lvl := (flevel fsrc fsgr fslo fshi mgr msw mlo mhi).
Notation sdf := (soundatf fpg fsgr fsbt).

(* what the source claims of a member, and what the level claims of one *)
Variable P Q : int -> int -> int -> Prop.

(* ---- what one write of the level owes ------------------------------------ *)

(* Every write the level makes is one word ored into one group of the page    *)
(* being filled.  These two say what such a write is worth -- one for the low *)
(* half of a source word and one for the high half -- and they are the whole  *)
(* of what the fold tables have to mean.  A member that reads a bit of the    *)
(* word written is one move of H out from a member the source had.            *)

Notation srcw r k := (PArray.get fsrc (Uint63.add (Uint63.mul r nhi) k)).

Hypothesis Qlo : forall src r k g pg gr bt,
  (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat g < ngroupn)%N ->
  sdf P src ->
  let w := srcw r k in
  let v := PArray.get (PArray.get src (pchk (fkpt w)))
             (Uint63.add (poff (fkpt w)) g) in
  let lo := Uint63.land v lo12 in
  let l := PArray.get mlo
             (Uint63.add (Uint63.lsl k 12)
                (PArray.get fslo (Uint63.add (Uint63.lsl (fren w) 12) lo))) in
  let X := if Uint63.eqb (PArray.get msw k) 0 then l else Uint63.lsl l 12 in
  let G := PArray.get mgr
             (Uint63.add
                (Uint63.mul
                   (PArray.get fsgr
                      (Uint63.add
                         (Uint63.mul
                            (Uint63.add (Uint63.mul (fren w) 2) (fpar w))
                            ngroupi) g)) nhi) k) in
  pchk r = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff r) G
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
      (sgrmv fsgr (fren (PArray.get fpg pg))
         (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
  ~~ (Uint63.land X
        (bitof (sbtmv fsbt (fren (PArray.get fpg pg)) bt)) =? 0) ->
  Q pg gr bt.

Hypothesis Qhi : forall src r k g pg gr bt,
  (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat g < ngroupn)%N ->
  sdf P src ->
  let w := srcw r k in
  let v := PArray.get (PArray.get src (pchk (fkpt w)))
             (Uint63.add (poff (fkpt w)) g) in
  let hi := Uint63.land (Uint63.lsr v 12) lo12 in
  let h := PArray.get mhi
             (Uint63.add (Uint63.lsl k 12)
                (PArray.get fshi (Uint63.add (Uint63.lsl (fren w) 12) hi))) in
  let X := if Uint63.eqb (PArray.get msw k) 0 then Uint63.lsl h 12 else h in
  let G := PArray.get mgr
             (Uint63.add
                (Uint63.mul
                   (PArray.get fsgr
                      (Uint63.add
                         (Uint63.mul
                            (Uint63.add (Uint63.mul (fren w) 2)
                               (Uint63.sub 1 (fpar w)))
                            ngroupi) g)) nhi) k) in
  pchk r = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff r) G
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
      (sgrmv fsgr (fren (PArray.get fpg pg))
         (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
  ~~ (Uint63.land X
        (bitof (sbtmv fsbt (fren (PArray.get fpg pg)) bt)) =? 0) ->
  Q pg gr bt.

(* and a member the source claims is claimed by the level too, one level on *)
Hypothesis PQ : forall pg gr bt, P pg gr bt -> Q pg gr bt.

Lemma sdfW src : sdf P src -> sdf Q src.
Proof. by move=> h pg gr bt ht; apply: PQ; apply: h. Qed.

(* ---- one write, read as a map write -------------------------------------- *)

(* Every write the level makes is this: one word ored into one group of the   *)
(* page being filled.  ffor_setp turns the array write into the map write and *)
(* soundatf_ffor says what it costs.                                          *)
Lemma lvstep d r bb G X :
  (pchk r <? PArray.length d) ->
  sdf Q (PArray.set d (pchk r) bb) ->
  (forall pg gr bt,
     pchk r = pchk (fkpt (PArray.get fpg pg)) ->
     Uint63.add (poff r) G
     = Uint63.add (poff (fkpt (PArray.get fpg pg)))
         (sgrmv fsgr (fren (PArray.get fpg pg))
            (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
     ~~ (Uint63.land X
           (bitof (sbtmv fsbt (fren (PArray.get fpg pg)) bt)) =? 0) ->
     Q pg gr bt) ->
  sdf Q (PArray.set d (pchk r)
           (PArray.set bb (Uint63.add (poff r) G)
              (Uint63.lor (PArray.get bb (Uint63.add (poff r) G)) X))).
Proof.
move=> hin hbb hnew.
by rewrite (ffor_setp _ _ _ hin); apply: soundatf_ffor.
Qed.

(* A HALF THAT IS ALL NOUGHTS IS NOT WRITTEN AT ALL.  Each of the two writes  *)
(* the level makes for a group is under a test, and this is that write with   *)
(* its test: nothing to say when it does not happen.                          *)
Lemma lvstep_if d r bb (c : bool) G X :
  (pchk r <? PArray.length d) ->
  sdf Q (PArray.set d (pchk r) bb) ->
  (forall pg gr bt,
     pchk r = pchk (fkpt (PArray.get fpg pg)) ->
     Uint63.add (poff r) G
     = Uint63.add (poff (fkpt (PArray.get fpg pg)))
         (sgrmv fsgr (fren (PArray.get fpg pg))
            (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
     ~~ (Uint63.land X
           (bitof (sbtmv fsbt (fren (PArray.get fpg pg)) bt)) =? 0) ->
     Q pg gr bt) ->
  sdf Q (PArray.set d (pchk r)
           (if c then bb
            else PArray.set bb (Uint63.add (poff r) G)
                   (Uint63.lor (PArray.get bb (Uint63.add (poff r) G)) X))).
Proof. by move=> hin hbb hnew; case: c => //; apply: lvstep. Qed.

(* ---- one move of H, gathered into the page being filled ------------------ *)

Lemma flevmv_sound src d r k b :
  (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  (pchk r <? PArray.length d) ->
  sdf P src ->
  sdf Q (PArray.set d (pchk r) b) ->
  sdf Q (PArray.set d (pchk r) (lvmv src r k (poff r) b)).
Proof.
move=> hr hk hin hsrc hb; rewrite /flevmv; cbv zeta.
apply: (@ifold_indi _ (fun b' => sdf Q (PArray.set d (pchk r) b')));
    [by apply: ltnW; exact: ngroupn_nwB| |exact: hb].
move=> g b' hg hb'; cbv zeta.
case: ifP => _ //.
(* the high half, on whatever the low half left *)
apply: lvstep_if => //.
  (* and the low half, on the page as it stands *)
  by apply: lvstep_if => // pg gr bt h1 h2 h3;
     apply: (Qlo hr hk hg hsrc h1 h2 h3).
by move=> pg gr bt h1 h2 h3; apply: (Qhi hr hk hg hsrc h1 h2 h3).
Qed.

(* ---- one kept page: the carry, then the ten moves ------------------------ *)

Lemma flevpg_sound src d r :
  (to_nat r < nrepn)%N -> (pchk r <? PArray.length d) ->
  sdf P src -> sdf Q d -> sdf Q (lvpg src r d).
Proof.
move=> hr hin hsrc hd; rewrite /flevpg; cbv zeta.
(* the ten moves, on top of the carry *)
apply: (@ifold_indi _ (fun b => sdf Q (PArray.set d (pchk r) b)));
    [by apply: ltnW; apply: (@ltn_nwB 4)|by move=> k b hk hb;
       apply: flevmv_sound|].
(* and the carry, which claims nothing the source did not *)
apply: (@ifold_indi _ (fun b => sdf Q (PArray.set d (pchk r) b)));
    [by apply: ltnW; exact: ngroupn_nwB| |by rewrite set_getA].
move=> g b hg hb; cbv zeta.
by apply: soundatf_copy => //; apply: sdfW.
Qed.

(* ---- and the level, over the pages it keeps ------------------------------ *)

Lemma flevel_sound src dst :
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length dst)) ->
  sdf P src -> sdf Q dst -> sdf Q (lvl src dst).
Proof.
move=> hlen hsrc hd; rewrite /flevel.
(* THE LENGTH DOES NOT MOVE, so the chunk of every kept page stays in range  *)
(* however many pages have been filled.  It is carried along beside          *)
(* soundness, and dropped at the end.                                        *)
set f := (fun r d => flevpg _ _ _ _ _ _ _ _ src r d).
have [h _] : sdf Q (ifold nrepn 0 f dst) /\
             PArray.length (ifold nrepn 0 f dst) = PArray.length dst; last first.
  exact: h.
apply: (@ifold_indi _ (fun d => sdf Q d /\
          PArray.length d = PArray.length dst));
    [by apply: ltnW; exact: to_nat_bounded| |by split].
move=> r d hr [hq hl]; split; last first.
  by rewrite /f /flevpg RowMap.length_setA.
by rewrite /f; apply: flevpg_sound => //; rewrite hl; apply: hlen.
Qed.

End FoldLvl.
