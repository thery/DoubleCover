(* =========================================================================  *)
(*  RowFoldLvl.v -- one folded level keeps a map sound.                       *)
(* =========================================================================  *)

(* A bit the level writes is a member one move of H further out than a bit    *)
(* the source had.  The level fills one page array and puts the chunk back    *)
(* once, so the induction reads: the map with this chunk put back is sound.   *)

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

(* ---- what one write of the level owes ------------------------------------ *)

(* Every write the level makes is one word ored into one group of the page    *)
(* being filled.  These two say what such a write is worth -- one for the low *)
(* half of a source word and one for the high half -- and they are the whole  *)
(* of what the fold tables have to mean.  A member that reads a bit of the    *)
(* word written is one move of H out from a member the source had.            *)
(*                                                                            *)
(* They are named rather than left as hypotheses of the section below because *)
(* the run asks for them at every depth, of the pair (Pd d, Pd d.+1).         *)

(* ONE WRITE, AND WHICH HALF OF THE CELL IT GOES TO.  A cell holds two kept   *)
(* pages, so the level writes twice for one source word: once for the         *)
(* destination's half nought, once for its half one.  They differ in three    *)
(* things and this says all three -- which half of the source is read, which  *)
(* renaming reads it, and where the answer lands.  fsrc carries the first     *)
(* pair, fsrc2 the second.                                                    *)
Definition Qlo_st (fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi : arr)
                  (P Q : int -> int -> int -> Prop) : Prop :=
forall src r k h g pg gr bt,
  (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  (to_nat g < ngroupn)%N ->
  (* A CELL THAT TAU FIXES HAS NO HALF ONE, and nothing is ever written to  *)
  (* one: fful says the cell is full, and the level does not call for it.   *)
  ~~ ((Uint63.eqb h 1) && Uint63.eqb (PArray.get fful r) allbits24) ->
  soundatf fpg fsgr fsbt P src ->
  let w := PArray.get fsrc (Uint63.add (Uint63.mul r nhi) k) in
  let w2 := PArray.get fsrc2 (Uint63.add (Uint63.mul r nhi) k) in
  let u := if Uint63.eqb h 0 then fren w else Uint63.lsr w2 1 in
  let sh := if Uint63.eqb h 0 then fhlf w else Uint63.land w2 1 in
  let v := PArray.get (PArray.get src (pchk (fkpt w)))
             (Uint63.add (poff (fkpt w)) g) in
  let vh := if Uint63.eqb sh 0 then Uint63.land v allbits24
            else Uint63.land (Uint63.lsr v nbiti) allbits24 in
  let lo := Uint63.land vh lo12 in
  let l := PArray.get mlo
             (Uint63.add (Uint63.lsl k 12)
                (PArray.get fslo (Uint63.add (Uint63.lsl u 12) lo))) in
  let X := Uint63.lsl l
             (fofs h (if Uint63.eqb (PArray.get msw k) 0 then 0 else 12)) in
  let G := PArray.get mgr
             (Uint63.add
                (Uint63.mul
                   (PArray.get fsgr
                      (Uint63.add
                         (Uint63.mul
                            (Uint63.add (Uint63.mul u 2) (fpar w))
                            ngroupi) g)) nhi) k) in
  inrange24 pg gr bt ->
  pchk r = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff r) G
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
      (sgrmv fsgr (fren (PArray.get fpg pg))
         (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
  ~~ (Uint63.land X
        (bitof (fbit (fhlf (PArray.get fpg pg))
                     (sbtmv fsbt (fren (PArray.get fpg pg)) bt))) =? 0) ->
  Q pg gr bt.

(* and the same for the high half of the source word                          *)
Definition Qhi_st (fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi : arr)
                  (P Q : int -> int -> int -> Prop) : Prop :=
forall src r k h g pg gr bt,
  (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  (to_nat g < ngroupn)%N ->
  (* A CELL THAT TAU FIXES HAS NO HALF ONE, and nothing is ever written to  *)
  (* one: fful says the cell is full, and the level does not call for it.   *)
  ~~ ((Uint63.eqb h 1) && Uint63.eqb (PArray.get fful r) allbits24) ->
  soundatf fpg fsgr fsbt P src ->
  let w := PArray.get fsrc (Uint63.add (Uint63.mul r nhi) k) in
  let w2 := PArray.get fsrc2 (Uint63.add (Uint63.mul r nhi) k) in
  let u := if Uint63.eqb h 0 then fren w else Uint63.lsr w2 1 in
  let sh := if Uint63.eqb h 0 then fhlf w else Uint63.land w2 1 in
  let v := PArray.get (PArray.get src (pchk (fkpt w)))
             (Uint63.add (poff (fkpt w)) g) in
  let vh := if Uint63.eqb sh 0 then Uint63.land v allbits24
            else Uint63.land (Uint63.lsr v nbiti) allbits24 in
  let hi := Uint63.land (Uint63.lsr vh 12) lo12 in
  let hb := PArray.get mhi
             (Uint63.add (Uint63.lsl k 12)
                (PArray.get fshi (Uint63.add (Uint63.lsl u 12) hi))) in
  let X := Uint63.lsl hb
             (fofs h (if Uint63.eqb (PArray.get msw k) 0 then 12 else 0)) in
  let G := PArray.get mgr
             (Uint63.add
                (Uint63.mul
                   (PArray.get fsgr
                      (Uint63.add
                         (Uint63.mul
                            (Uint63.add (Uint63.mul u 2)
                               (Uint63.sub 1 (fpar w)))
                            ngroupi) g)) nhi) k) in
  inrange24 pg gr bt ->
  pchk r = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff r) G
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
      (sgrmv fsgr (fren (PArray.get fpg pg))
         (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
  ~~ (Uint63.land X
        (bitof (fbit (fhlf (PArray.get fpg pg))
                     (sbtmv fsbt (fren (PArray.get fpg pg)) bt))) =? 0) ->
  Q pg gr bt.

Section FoldLvl.

(* the six tables a member is read and gathered through *)
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.

(* and the move, on groups, halves and bits *)
Variable mgr msw mlo mhi : arr.

Notation lvmv := (flevmv fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Notation lvpg := (flevpg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Notation lvl := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
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

Hypothesis Qlo : Qlo_st fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi P Q.
Hypothesis Qhi : Qhi_st fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi P Q.

(* and a member the source claims is claimed by the level too, one level on *)
Hypothesis PQ : forall pg gr bt, P pg gr bt -> Q pg gr bt.

Lemma sdfW src : sdf P src -> sdf Q src.
Proof. by move=> h pg gr bt hr ht; apply: PQ; apply: (h _ _ _ hr ht). Qed.

(* ---- one write, read as a map write -------------------------------------- *)

(* Every write the level makes is this: one word ored into one group of the   *)
(* page being filled.  ffor_setp turns the array write into the map write and *)
(* soundatf_ffor says what it costs.                                          *)
Lemma lvstep d r bb G X :
  (pchk r <? PArray.length d) ->
  sdf Q (PArray.set d (pchk r) bb) ->
  (forall pg gr bt, inrange24 pg gr bt ->
     pchk r = pchk (fkpt (PArray.get fpg pg)) ->
     Uint63.add (poff r) G
     = Uint63.add (poff (fkpt (PArray.get fpg pg)))
         (sgrmv fsgr (fren (PArray.get fpg pg))
            (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
     ~~ (Uint63.land X
           (bitof (fbit (fhlf (PArray.get fpg pg))
                     (sbtmv fsbt (fren (PArray.get fpg pg)) bt))) =? 0) ->
     Q pg gr bt) ->
  sdf Q (PArray.set d (pchk r)
           (PArray.set bb (Uint63.add (poff r) G)
              (Uint63.lor (PArray.get bb (Uint63.add (poff r) G)) X))).
Proof.
move=> hin hbb hnew.
by rewrite (ffor_setp _ _ _ hin); apply: soundatf_or.
Qed.

(* A HALF THAT IS ALL NOUGHTS IS NOT WRITTEN AT ALL.  Each of the two writes  *)
(* the level makes for a group is under a test, and this is that write with   *)
(* its test: nothing to say when it does not happen.                          *)
Lemma lvstep_if d r bb (c : bool) G X :
  (pchk r <? PArray.length d) ->
  sdf Q (PArray.set d (pchk r) bb) ->
  (forall pg gr bt, inrange24 pg gr bt ->
     pchk r = pchk (fkpt (PArray.get fpg pg)) ->
     Uint63.add (poff r) G
     = Uint63.add (poff (fkpt (PArray.get fpg pg)))
         (sgrmv fsgr (fren (PArray.get fpg pg))
            (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
     ~~ (Uint63.land X
           (bitof (fbit (fhlf (PArray.get fpg pg))
                     (sbtmv fsbt (fren (PArray.get fpg pg)) bt))) =? 0) ->
     Q pg gr bt) ->
  sdf Q (PArray.set d (pchk r)
           (if c then bb
            else PArray.set bb (Uint63.add (poff r) G)
                   (Uint63.lor (PArray.get bb (Uint63.add (poff r) G)) X))).
Proof. by move=> hin hbb hnew; case: c => //; apply: lvstep. Qed.

(* ---- one half of a cell, moved: two writes ------------------------------ *)

(* flevmvu is the low twelve bits then the high twelve, each under its own    *)
(* test.  This is those two writes as one lemma, so that flevmv_sound can     *)
(* use it once for each half of the cell instead of writing the pair out      *)
(* twice.                                                                     *)
Lemma flevmvu_sound d r k vh dh glo ghi ub kb sw bb :
  (pchk r <? PArray.length d) ->
  sdf Q (PArray.set d (pchk r) bb) ->
  (forall pg gr bt, inrange24 pg gr bt ->
     pchk r = pchk (fkpt (PArray.get fpg pg)) ->
     Uint63.add (poff r)
       (PArray.get mgr
          (Uint63.add (Uint63.mul (PArray.get fsgr glo) nhi) k))
     = Uint63.add (poff (fkpt (PArray.get fpg pg)))
         (sgrmv fsgr (fren (PArray.get fpg pg))
            (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
     ~~ (Uint63.land
           (Uint63.lsl
              (PArray.get mlo
                 (Uint63.add kb
                    (PArray.get fslo
                       (Uint63.add ub (Uint63.land vh lo12)))))
              (fofs dh (if sw then 0 else 12)))
           (bitof (fbit (fhlf (PArray.get fpg pg))
                     (sbtmv fsbt (fren (PArray.get fpg pg)) bt))) =? 0) ->
     Q pg gr bt) ->
  (forall pg gr bt, inrange24 pg gr bt ->
     pchk r = pchk (fkpt (PArray.get fpg pg)) ->
     Uint63.add (poff r)
       (PArray.get mgr
          (Uint63.add (Uint63.mul (PArray.get fsgr ghi) nhi) k))
     = Uint63.add (poff (fkpt (PArray.get fpg pg)))
         (sgrmv fsgr (fren (PArray.get fpg pg))
            (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
     ~~ (Uint63.land
           (Uint63.lsl
              (PArray.get mhi
                 (Uint63.add kb
                    (PArray.get fshi
                       (Uint63.add ub
                          (Uint63.land (Uint63.lsr vh 12) lo12)))))
              (fofs dh (if sw then 12 else 0)))
           (bitof (fbit (fhlf (PArray.get fpg pg))
                     (sbtmv fsbt (fren (PArray.get fpg pg)) bt))) =? 0) ->
     Q pg gr bt) ->
  sdf Q (PArray.set d (pchk r)
           (flevmvu fslo fshi mlo mhi mgr fsgr vh dh (poff r)
              glo ghi ub kb k sw bb)).
Proof.
move=> hin hbb hlo hhi; rewrite /flevmvu; cbv zeta.
case: ifP => _ //.
apply: lvstep_if => //.
by apply: lvstep_if => //.
Qed.

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
have h0L : (to_nat 0%uint63 < 2)%N by rewrite to_nat_0.
have h1L : (to_nat 1%uint63 < 2)%N by rewrite to_nat_1.
(* half nought is always there, so its side condition is settled once *)
have h0G : ~~ ((Uint63.eqb 0 1) && Uint63.eqb (PArray.get fful r) allbits24).
  by have -> : (Uint63.eqb 0 1) = false by vm_compute.
(* A CELL IS TWO KEPT PAGES, so one source word is moved twice: into the      *)
(* destination's half nought, and into its half one where there is one.  Each *)
(* of those is flevmvu -- the low twelve bits then the high -- and each is    *)
(* Qlo and Qhi at that half.  THE TEST THAT PICKS THE SECOND HALF IS EXACTLY  *)
(* THE SIDE CONDITION Qlo and Qhi ask for at half one.                        *)
case: ifP => hif; last first.
  apply: flevmvu_sound => // pg gr bt h1 h2 h3.
  - exact: (Qlo hr hk h0L hg h0G hsrc h1 h2 h3).
  exact: (Qhi hr hk h0L hg h0G hsrc h1 h2 h3).
have h1G : ~~ ((Uint63.eqb 1 1) && Uint63.eqb (PArray.get fful r) allbits24).
  by move: hif; rewrite andbC andbT.
apply: flevmvu_sound => //.
- apply: flevmvu_sound => // pg gr bt h1 h2 h3.
  - exact: (Qlo hr hk h0L hg h0G hsrc h1 h2 h3).
  exact: (Qhi hr hk h0L hg h0G hsrc h1 h2 h3).
- move=> pg gr bt h1 h2 h3; exact: (Qlo hr hk h1L hg h1G hsrc h1 h2 h3).
move=> pg gr bt h1 h2 h3; exact: (Qhi hr hk h1L hg h1G hsrc h1 h2 h3).
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

(* ---- the level does not change how long the map is ----------------------- *)

Lemma flevel_length src dst :
  PArray.length (lvl src dst) = PArray.length dst.
Proof.
rewrite /flevel.
apply: (@ifold_indi _ (fun d => PArray.length d = PArray.length dst));
    [by apply: ltnW; exact: to_nat_bounded| |by []].
by move=> r d hr hl; rewrite /flevpg RowMap.length_setA.
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
set f := (fun r d => flevpg _ _ _ _ _ _ _ _ _ _ src r d).
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

(* =========================================================================  *)
(*  The run: the levels one after another, at growing depths.                 *)
(* =========================================================================  *)

Section FoldRun.

Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.

Notation lvl := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Notation sdf := (soundatf fpg fsgr fsbt).

(* what the map claims of a member at each depth: for the row, that it is    *)
(* within that many moves                                                     *)
Variable Pd : nat -> int -> int -> int -> Prop.

Hypothesis PdW : forall d pg gr bt, Pd d pg gr bt -> Pd d.+1 pg gr bt.

Hypothesis Qlod : forall d,
  Qlo_st fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi (Pd d) (Pd d.+1).
Hypothesis Qhid : forall d,
  Qhi_st fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi (Pd d) (Pd d.+1).

(* THE SEARCH IS NOT REDONE HERE.  A level is the gather and then, at the     *)
(* depths it is asked for, a search that marks what it reaches -- the mark is *)
(* RowFoldOk.soundatf_fmark and the tree is RowRun's induction.  All the run  *)
(* needs of it is that whatever it does to the map it leaves it sound at the  *)
(* depth it was called at, and leaves it as long as it found it.              *)
Variable ext : nat -> rmap -> rmap.
Hypothesis extP : forall d m, sdf (Pd d) m -> sdf (Pd d) (ext d m).
Hypothesis extlen : forall d m, PArray.length (ext d m) = PArray.length m.

Definition flvlx (d : nat) (m dst : rmap) : rmap := ext d (lvl m dst).

Fixpoint frunx (n d : nat) (m dst : rmap) : rmap :=
  if n is n1.+1 then frunx n1 d.+1 (flvlx d.+1 m dst) m else m.

(* a map sound at d is sound at d plus one, which is what carrying it over    *)
(* costs                                                                      *)
Lemma sdfWd d m : sdf (Pd d) m -> sdf (Pd d.+1) m.
Proof. by move=> h pg gr bt hr ht; apply: PdW; apply: (h _ _ _ hr ht). Qed.

Lemma flvlx_sound d m dst :
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length dst)) ->
  sdf (Pd d) m -> sdf (Pd d.+1) dst -> sdf (Pd d.+1) (flvlx d.+1 m dst).
Proof.
move=> hlen hm hd; rewrite /flvlx.
apply: extP.
exact: (@flevel_sound fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
          (Pd d) (Pd d.+1) (@Qlod d) (@Qhid d)
          (fun pg gr bt (h : Pd d pg gr bt) => @PdW d pg gr bt h)
          m dst hlen hm hd).
Qed.

(* ---- and the run, which is the levels one after another ------------------ *)

Lemma frunx_sound n d m dst :
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length m)) ->
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length dst)) ->
  sdf (Pd d) m -> sdf (Pd d) dst -> sdf (Pd (d + n)) (frunx n d m dst).
Proof.
elim: n d m dst => [|n ih] d m dst hlm hld hm hd /=; first by rewrite addn0.
rewrite addnS -addSn.
apply: ih => //.
- by move=> r hr; rewrite /flvlx extlen flevel_length; apply: hld.
- by apply: flvlx_sound => //; apply: sdfWd.
by apply: sdfWd.
Qed.

End FoldRun.
