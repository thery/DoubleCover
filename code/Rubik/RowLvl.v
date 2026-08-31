(* =========================================================================  *)
(*  RowLvl.v -- the prepass, reading the move's groups by one addition.       *)
(* =========================================================================  *)

(* RowMap's prepass reads the move's new group as mgr[gr * 10 + k]: a         *)
(* multiply and an add for every word of the map, 813 million words a move,   *)
(* ten moves a level.  rubik_row_nofold.ml does not: it copies the move's     *)
(* whole column into a flat array once, and the inner loop is one indexed     *)
(* read.                                                                      *)
(*                                                                            *)
(* THE COLUMN IS NOT BUILT AT RUN TIME HERE.  It is the same table            *)
(* transposed -- mgrT[k * 20160 + gr] -- so the instance builds it once and   *)
(* checks it once, and the loop reads mgrT[base + gr] with base fixed for the *)
(* move.  One addition a word.                                                *)
(*                                                                            *)
(* NOTHING NEW IS PROVED ABOUT THE CUBE.  The new prepass is shown EQUAL to   *)
(* RowMap's, so RowRun.prepass_sound carries straight over.                   *)
(*                                                                            *)
(* A file of its own because RowMap is read by the folded run.                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- two walks that take the same step are the same walk ----------------- *)

Lemma ifold_eqg (A : Type) n j (f g : int -> A -> A) a :
  (j + n <= nwB)%N ->
  (forall k b, (to_nat k < j + n)%N -> f k b = g k b) ->
  ifold n (advn j 0) f a = ifold n (advn j 0) g a.
Proof.
elim: n j a => [|n ih] j a hb hf //=.
have -> : Uint63.add (advn j 0) 1 = advn j.+1 0 by rewrite advnS.
have hj : (to_nat (advn j 0) < j + n.+1)%N.
  rewrite to_nat_advn0; first by rewrite addnS ltnS leq_addr.
  by apply: leq_trans hb; rewrite addnS ltnS leq_addr.
rewrite hf //; apply: ih; first by rewrite addSnnS.
by move=> k b hk; apply: hf; rewrite -addSnnS.
Qed.

Lemma ifold_eqi (A : Type) n (f g : int -> A -> A) a :
  (n <= nwB)%N ->
  (forall k b, (to_nat k < n)%N -> f k b = g k b) ->
  ifold n 0 f a = ifold n 0 g a.
Proof. by move=> hb hf; apply: (@ifold_eqg _ n 0). Qed.

(* the split the chunk arithmetic rests on, over plain variables so that     *)
(* nothing in it can be evaluated                                            *)
Lemma addn_divmod a b c : (0 < c)%N ->
  (a + b)%N = ((a %/ c) * c + (a %% c + b))%N.
Proof. by move=> hc; rewrite addnA -divn_eq. Qed.

(* ---- writing one chunk of the map, and putting it back once -------------- *)

(* flevpg pulls the destination chunk out of the outer array, writes into it  *)
(* for the whole page, and puts it back once.  RowMap's gor puts it back at   *)
(* every word.  These three say the two are the same, and none of them        *)
(* mentions the cube.                                                         *)

Lemma set_getA (t : rmap) (i : int) : (i <? PArray.length t) ->
  PArray.set t i (PArray.get t i) = t.
Proof.
move=> hi; apply: PArray.array_ext.
- exact: (length_setA t i (PArray.get t i)).
- move=> j _; have [hij|hij] := boolP (i =? j)%uint63.
    have hije : i = j by apply: to_nat_inj; apply/neqbP.
    by rewrite -hije get_setA.
  have hne : i <> j.
    by move=> he; move: hij; rewrite he; case: neqbP.
  by rewrite get_set_otherA.
- exact: (default_setA t i (PArray.get t i)).
Qed.

Lemma set_setA (t : rmap) (i : int) (u v : arr) :
  PArray.set (PArray.set t i u) i v = PArray.set t i v.
Proof.
apply: PArray.array_ext.
- by rewrite !length_setA.
- move=> j _; have [hij|hij] := boolP (i =? j)%uint63.
    have hije : i = j by apply: to_nat_inj; apply/neqbP.
    have [hin|hin] := boolP (i <? PArray.length t)%uint63.
      by rewrite -hije !get_setA ?length_setA.
    rewrite -hije !get_oobA ?default_setA //;
      by rewrite !length_setA; apply: negbTE.
  have hne : i <> j.
    by move=> he; move: hij; rewrite he; case: neqbP.
  by rewrite !get_set_otherA.
- by rewrite !default_setA.
Qed.

Lemma fold_in_chunkg c (f : int -> arr -> arr) d n j :
  (c <? PArray.length d) ->
  ifold n (advn j 0) (fun i a => PArray.set a c (f i (PArray.get a c))) d
  = PArray.set d c (ifold n (advn j 0) f (PArray.get d c)).
Proof.
elim: n j d => [|n ih] j d hc /=; first by rewrite set_getA.
have -> : Uint63.add (advn j 0) 1 = advn j.+1 0 by rewrite advnS.
rewrite ih ?length_setA // get_setA //.
by rewrite set_setA.
Qed.

Lemma fold_in_chunk c (f : int -> arr -> arr) d n :
  (c <? PArray.length d) ->
  ifold n 0 (fun i a => PArray.set a c (f i (PArray.get a c))) d
  = PArray.set d c (ifold n 0 f (PArray.get d c)).
Proof. by move=> hc; apply: (@fold_in_chunkg c f d n 0). Qed.

Section Lvl.

(* ---- the ten moves of H, as RowMap reads them ---------------------------- *)

Variable mpg mgr msw mlo mhi : arr.

Local Notation pgm := (pgmv mpg).
Local Notation grm := (grmv mgr).
Local Notation grpm := (grpmv msw mlo mhi).

(* ---- and the same group table, transposed -------------------------------- *)

(* mgrT[k * 20160 + gr] is what mgr[gr * 10 + k] is.  The instance builds it  *)
(* and checks it; nothing here says where it comes from.                      *)
Variable mgrT : arr.

Definition grmT (base gr : int) : int := PArray.get mgrT (Uint63.add base gr).

Hypothesis mgrT_ok : forall k gr, (to_nat k < nhn)%N ->
  (to_nat gr < ngroupn)%N ->
  grmT (Uint63.mul k ngroupi) gr = grm k gr.

(* ---- a page sits inside one chunk, and then a read is one array get ------ *)

(* gget finds the chunk again for every word: a get on the outer array and a  *)
(* get on the chunk.  A page is 20160 consecutive words, so unless it lies    *)
(* across a chunk boundary the chunk is the same for the whole page and is    *)
(* read once.  That is what flevpg does.                                      *)
(*                                                                            *)
(* SOME PAGES DO LIE ACROSS A BOUNDARY, because a chunk is 2^21 words and a   *)
(* page is 20160, which does not divide it.  Those take the old road.  The    *)
(* fold has none: its chunk is 64 whole pages.                                *)
(*                                                                            *)
(* NOT ONE NUMBER IS BUILT IN UNARY BELOW.  Every bound is an int63 test that *)
(* vm_compute settles, lifted by nltbP, nlebP or to_nat_add_le; a nat of two  *)
(* million, let alone of eight hundred million, does not finish.              *)

Definition pgbase (pg : int) : int := grpof pg 0.
Definition pgchk (pg : int) : int := Uint63.div (pgbase pg) csize.
Definition pgoff (pg : int) : int := Uint63.mod (pgbase pg) csize.

(* the page is inside its chunk, and the second test is what says the first   *)
(* addition did not wrap                                                      *)
Definition pgfits (pg : int) : bool :=
  (Uint63.add (pgoff pg) ngroupi <=? csize) &&
  (pgoff pg <=? Uint63.add (pgoff pg) ngroupi).

(* NO `//' ON A SIDE GOAL ABOUT A SIZE.  `//' is `done', and `done' unfolds  *)
(* and evaluates: 0 < to_nat csize sends it away to build two million in     *)
(* unary and it does not come back.  Every one is handed its proof.          *)

Lemma zero_ngroupi : (0 <? ngroupi)%uint63.
Proof. by []. Qed.

Lemma pgbase_nat pg : (pg <? npagei) ->
  to_nat (pgbase pg) = (to_nat pg * ngroupn)%N.
Proof.
move=> hpg; rewrite /pgbase (to_nat_grpof hpg zero_ngroupi).
by rewrite to_nat_0 addn0.
Qed.

Lemma pgfits_nat pg : pgfits pg ->
  (to_nat (pgoff pg) + ngroupn <= to_nat csize)%N.
Proof.
case/andP => /nlebP hle hno.
by rewrite -(to_nat_add_le _ _ hno) -/ngroupn.
Qed.

(* THE TWO INDEX FACTS.  The read uses them, and so does the write: a page   *)
(* inside one chunk has the same chunk for all its words, and the offset is   *)
(* the page's own plus the group.                                             *)
Lemma pgidx pg gr : (pg <? npagei) -> (gr <? ngroupi) -> pgfits pg ->
  Uint63.div (grpof pg gr) csize = pgchk pg
  /\ Uint63.mod (grpof pg gr) csize = Uint63.add (pgoff pg) gr.
Proof.
move=> hpg hgr hfit.
have hb : to_nat (pgbase pg) = (to_nat pg * ngroupn)%N := pgbase_nat hpg.
have hg : to_nat (grpof pg gr) = (to_nat pg * ngroupn + to_nat gr)%N :=
  to_nat_grpof hpg hgr.
have hgrn : (to_nat gr < ngroupn)%N := ltn_ngroupi hgr.
have hfn := pgfits_nat hfit.
have hgn : (0 < ngroupn)%N := leq_ltn_trans (leq0n _) hgrn.
have hcs : (0 < to_nat csize)%N :=
  leq_trans hgn (leq_trans (leq_addl _ _) hfn).
have hoff : to_nat (pgoff pg) = ((to_nat pg * ngroupn) %% to_nat csize)%N.
  rewrite /pgoff to_nat_mod hb; reflexivity.
have hlow : ((to_nat pg * ngroupn) %% to_nat csize + to_nat gr
             < to_nat csize)%N.
  rewrite -hoff; apply: leq_trans hfn; rewrite ltn_add2l; exact: hgrn.
have hsplit := addn_divmod (to_nat pg * ngroupn) (to_nat gr) hcs.
have hlow2 : (to_nat (pgoff pg) + to_nat gr < to_nat csize)%N.
  rewrite hoff; exact: hlow.
(* THE nwB SIDE GOAL IS NOT LEFT TO `by'.  nwB is 2^63 in unary.            *)
have hadd : to_nat (Uint63.add (pgoff pg) gr)
          = (to_nat (pgoff pg) + to_nat gr)%N.
  apply: to_nat_add; apply: (@leq_trans (to_nat csize)).
    exact: hlow2.
  exact: (ltnW (to_nat_bounded csize)).
(* EVERY REWRITE IS GIVEN ITS SIDE AND ITS ARGUMENTS.  Left to search for   *)
(* its pattern, rewrite wanders into csize and does not come back.          *)
split.
{ apply: to_nat_inj.
  rewrite [LHS](to_nat_div (grpof pg gr) csize).
  rewrite hg hsplit.
  rewrite [LHS]divnMDl.
  rewrite [in LHS](divn_small hlow).
  rewrite addn0.
  rewrite /pgchk [RHS](to_nat_div (pgbase pg) csize) hb.
  reflexivity.
  (* divnMDl leaves its own 0 < d behind and must be handed hcs *)
  exact: hcs. }
apply: to_nat_inj.
rewrite [LHS](to_nat_mod (grpof pg gr) csize).
rewrite hg hsplit.
rewrite [LHS]modnMDl.
rewrite [LHS](modn_small hlow).
rewrite hadd hoff.
reflexivity.
Qed.

Lemma pgread src pg gr : (pg <? npagei) -> (gr <? ngroupi) -> pgfits pg ->
  gget src (grpof pg gr)
  = PArray.get (PArray.get src (pgchk pg)) (Uint63.add (pgoff pg) gr).
Proof.
move=> hpg hgr hfit; have [hdiv hmod] := pgidx hpg hgr hfit.
by rewrite /gget cshftE cmskwE hdiv hmod.
Qed.

Lemma pgwrite d pg gr v : (pg <? npagei) -> (gr <? ngroupi) -> pgfits pg ->
  gor d (grpof pg gr) v
  = PArray.set d (pgchk pg)
      (PArray.set (PArray.get d (pgchk pg)) (Uint63.add (pgoff pg) gr)
         (Uint63.lor
            (PArray.get (PArray.get d (pgchk pg)) (Uint63.add (pgoff pg) gr))
            v)).
Proof.
move=> hpg hgr hfit; have [hdiv hmod] := pgidx hpg hgr hfit.
by rewrite /gor /gset /gget !cshftE !cmskwE hdiv hmod.
Qed.

(* ---- one move over the whole map, the base fixed for the move ------------ *)

Definition prepmvT (k : int) (src : rmap) (dst : rmap) : rmap :=
  let base := Uint63.mul k ngroupi in
  ifold npagen 0
    (fun pg d =>
       let pg' := pgm k pg in
       ifold ngroupn 0
         (fun gr d' =>
            let v := gget src (grpof pg gr) in
            if Uint63.eqb v 0 then d'
            else gor d' (grpof pg' (grmT base gr)) (grpm k v))
         d)
    dst.

Definition prepmv0T (k : int) (src : rmap) (dst : rmap) : rmap :=
  let base := Uint63.mul k ngroupi in
  ifold npagen 0
    (fun pg d =>
       let pg' := pgm k pg in
       ifold ngroupn 0
         (fun gr d' =>
            let g := grpof pg gr in
            let v := gget src g in
            if Uint63.eqb v 0 then d'
            else gor (gor d' g v) (grpof pg' (grmT base gr)) (grpm k v))
         d)
    dst.

Definition prepassT (src dst : rmap) : rmap :=
  ifold nhn 0
    (fun k d => if Uint63.eqb k 0 then prepmv0T k src d else prepmvT k src d)
    dst.

(* ---- the same, reading each page's chunk once ---------------------------- *)

(* This is flevpg's shape: the chunk out of the outer array once for the      *)
(* page, then one array read a word.  A page that lies across a boundary      *)
(* takes the old road, and there are few of them.                             *)

Definition prepmvS (k : int) (src : rmap) (dst : rmap) : rmap :=
  let base := Uint63.mul k ngroupi in
  ifold npagen 0
    (fun pg d =>
       let pg' := pgm k pg in
       if pgfits pg then
         let sa := PArray.get src (pgchk pg) in
         let o := pgoff pg in
         ifold ngroupn 0
           (fun gr d' =>
              let v := PArray.get sa (Uint63.add o gr) in
              if Uint63.eqb v 0 then d'
              else gor d' (grpof pg' (grmT base gr)) (grpm k v))
           d
       else
         ifold ngroupn 0
           (fun gr d' =>
              let v := gget src (grpof pg gr) in
              if Uint63.eqb v 0 then d'
              else gor d' (grpof pg' (grmT base gr)) (grpm k v))
           d)
    dst.

Definition prepmv0S (k : int) (src : rmap) (dst : rmap) : rmap :=
  let base := Uint63.mul k ngroupi in
  ifold npagen 0
    (fun pg d =>
       let pg' := pgm k pg in
       if pgfits pg then
         let sa := PArray.get src (pgchk pg) in
         let o := pgoff pg in
         ifold ngroupn 0
           (fun gr d' =>
              let g := grpof pg gr in
              let v := PArray.get sa (Uint63.add o gr) in
              if Uint63.eqb v 0 then d'
              else gor (gor d' g v) (grpof pg' (grmT base gr)) (grpm k v))
           d
       else
         ifold ngroupn 0
           (fun gr d' =>
              let g := grpof pg gr in
              let v := gget src g in
              if Uint63.eqb v 0 then d'
              else gor (gor d' g v) (grpof pg' (grmT base gr)) (grpm k v))
           d)
    dst.

Definition prepassS (src dst : rmap) : rmap :=
  ifold nhn 0
    (fun k d => if Uint63.eqb k 0 then prepmv0S k src d else prepmvS k src d)
    dst.

Lemma prepmvS_eq k src dst : prepmvS k src dst = prepmvT k src dst.
Proof.
rewrite /prepmvS /prepmvT; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: npagen_nwB.
move=> pg d hpg; cbv zeta.
have hpi : (pg <? npagei) := introT (nltbP pg npagei) hpg.
case: (boolP (pgfits pg)) => hfit; last by [].
apply: ifold_eqi; first by apply: ltnW; exact: ngroupn_nwB.
move=> gr d' hgr; cbv zeta.
have hgi : (gr <? ngroupi) := introT (nltbP gr ngroupi) hgr.
by rewrite -(pgread src hpi hgi hfit).
Qed.

Lemma prepmv0S_eq k src dst : prepmv0S k src dst = prepmv0T k src dst.
Proof.
rewrite /prepmv0S /prepmv0T; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: npagen_nwB.
move=> pg d hpg; cbv zeta.
have hpi : (pg <? npagei) := introT (nltbP pg npagei) hpg.
case: (boolP (pgfits pg)) => hfit; last by [].
apply: ifold_eqi; first by apply: ltnW; exact: ngroupn_nwB.
move=> gr d' hgr; cbv zeta.
have hgi : (gr <? ngroupi) := introT (nltbP gr ngroupi) hgr.
by rewrite -(pgread src hpi hgi hfit).
Qed.

(* ---- and it is RowMap's prepass ------------------------------------------ *)

Lemma prepmvT_eq k src dst : (to_nat k < nhn)%N ->
  prepmvT k src dst = prepmv mpg mgr msw mlo mhi k src dst.
Proof.
move=> hk; rewrite /prepmvT /prepmv; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: npagen_nwB.
move=> pg d _; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: ngroupn_nwB.
by move=> gr d' hgr; rewrite mgrT_ok.
Qed.

Lemma prepmv0T_eq k src dst : (to_nat k < nhn)%N ->
  prepmv0T k src dst = prepmv0 mpg mgr msw mlo mhi k src dst.
Proof.
move=> hk; rewrite /prepmv0T /prepmv0; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: npagen_nwB.
move=> pg d _; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: ngroupn_nwB.
by move=> gr d' hgr; rewrite mgrT_ok.
Qed.

Lemma prepassT_eq src dst :
  prepassT src dst = prepass mpg mgr msw mlo mhi src dst.
Proof.
rewrite /prepassT /prepass.
apply: ifold_eqi; first by apply: ltnW; apply: (@ltn_nwB 4).
(* NOT `case: ifP'.  The two branches are whole prepasses and ifP reduces    *)
(* them: the stack overflows.  A plain case on the boolean only splits.      *)
move=> k d hk; case: (Uint63.eqb k 0).
  by rewrite prepmv0T_eq.
by rewrite prepmvT_eq.
Qed.

Lemma prepassS_eq src dst :
  prepassS src dst = prepass mpg mgr msw mlo mhi src dst.
Proof.
rewrite -prepassT_eq /prepassS /prepassT.
apply: ifold_eqi; first by apply: ltnW; apply: (@ltn_nwB 4).
move=> k d hk; case: (Uint63.eqb k 0).
  by rewrite prepmv0S_eq.
by rewrite prepmvS_eq.
Qed.

End Lvl.
