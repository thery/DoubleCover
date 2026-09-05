(* =========================================================================  *)
(*  RowMap48.v -- the map of a row at forty eight bits a cell.                *)
(* =========================================================================  *)

(* A cell is a corner PAIR and carries forty eight bits, so the map is        *)
(* 20160 pages of 20160 cells, 406 425 600 words, 3.25 GB -- half of what     *)
(* RowMap.v lays out.  The chunk is the same two million words, so there are  *)
(* 194 chunks where there were 388.                                           *)
(*                                                                            *)
(* MOST OF RowMap.v IS REUSED AS IT STANDS.  gget, gset, gor, mtest and mmark *)
(* say nothing about how wide a cell is, and the chunking is the same         *)
(* division by the same chunk size, so `gget_gset', `grp_eq' and `grpof_inj'  *)
(* carry over.  What is new is only what mentions the width: the empty map,   *)
(* which has its own number of chunks, and the full map, whose word is all    *)
(* forty eight bits.                                                          *)
(*                                                                            *)
(* A page number here is a corner pair, and a pair number is below the page   *)
(* count of RowMap.v, so every range fact of that file applies to it.         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row Row48 RowMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* ---- the map -------------------------------------------------------------- *)

Definition nchunk48i : int := 194%uint63.   (* 20160 * 20160 / 2 ^ 21         *)
Definition nchunk48n : nat := 194.

(* every chunk gets its own array, for RowMap's reason: one PArray.make run   *)
(* once would hand the same array to all 194 slots                            *)
Definition mkempty48 (u : unit) : rmap :=
  ifold nchunk48n 0%uint63
    (fun c a => PArray.set a c (PArray.make csize 0%uint63))
    (PArray.make nchunk48i (PArray.make 1%uint63 0%uint63)).

(* NEVER START A RUN FROM THIS ONE: a global is held for ever, so every       *)
(* difference ever made to it stays alive.  This is for reading.              *)
Definition mempty48 : rmap := mkempty48 tt.

(* the map is full when every cell has all forty eight bits                   *)
Definition allbits48 : int := 281474976710655%uint63.

Definition mfull48 (m : rmap) : bool :=
  iter nclsn 0%uint63
    (fun pg => iter ngroupn 0%uint63
       (fun gr => Uint63.eqb (gget m (grpof pg gr)) allbits48)).

(* ---- the bits ------------------------------------------------------------- *)

Lemma lt_digits48 x : (x <? nbit48i)%uint63 -> (x <? digits)%uint63.
Proof.
move=> h; apply/nltbP; apply: leq_trans (_ : to_nat nbit48i <= _).
  by apply/nltbP.
by apply/nlebP; vm_compute.
Qed.

Lemma allbits48P bt : (bt <? nbit48i)%uint63 ->
  (Uint63.land allbits48 (bitof bt) =? 0)%uint63 = false.
Proof.
move=> hb; have hbd := lt_digits48 hb.
have hset : bit (Uint63.land allbits48 (bitof bt)) bt.
  rewrite land_spec.
  have -> : allbits48 = decr (Uint63.lsl one nbit48i) by vm_compute.
  rewrite bit_decr ?hb //.
  rewrite /bitof; have -> : 1%uint63 = one by vm_compute.
  by rewrite bit_onenn // eqxx.
apply/negbTE/negP => /neqbP h0.
have hz : Uint63.land allbits48 (bitof bt) = 0%uint63 by apply: to_nat_inj.
by move: hset; rewrite hz bit_0.
Qed.

(* two of the forty eight bits meet only when they are the same bit           *)
Lemma bitof48_inj b bt : (b <? nbit48i)%uint63 -> (bt <? nbit48i)%uint63 ->
  ~~ (Uint63.land (bitof b) (bitof bt) =? 0)%uint63 -> b = bt.
Proof.
move=> hb hbt h; have hbd := lt_digits48 hb; have hbtd := lt_digits48 hbt.
case: (b =P bt) => // hne; case/negP: h.
have hz : Uint63.land (bitof b) (bitof bt) = 0%uint63.
  apply: bit_ext => i; rewrite land_spec bit_0.
  have [hid|hid] := boolP (i <? digits)%uint63; last first.
    have hd : (digits <=? i)%uint63.
      by apply/nlebP; rewrite leqNgt; apply/negP => /nltbP h1; case/negP: hid.
    by rewrite bit_M ?andbF.
  rewrite /bitof; have -> : 1%uint63 = one by vm_compute.
  rewrite !bit_onenn //.
  case: eqP => [hbi|_] //=; case: eqP => [hti|_] //=.
  by case: hne; rewrite hbi hti.
by rewrite hz; apply/neqbP.
Qed.

(* ---- a pair number is a page number, so RowMap's ranges serve ------------- *)

Lemma ltn_nclsi_npagei pg : (pg <? nclsi)%uint63 -> (pg <? npagei)%uint63.
Proof.
move=> h; apply/nltbP; apply: leq_trans (nltbP _ _ h) _.
by apply/nlebP; vm_compute.
Qed.

(* ---- the four facts the rest of the development uses ---------------------- *)

(* an empty map has no bit set                                                *)
Lemma get_mkempty48 c :
  PArray.get (mkempty48 tt) c = PArray.make csize 0%uint63 \/
  PArray.get (mkempty48 tt) c = PArray.make 1%uint63 0%uint63.
Proof.
have hset : forall (t : rmap) i (v : arr),
    PArray.get (PArray.set t i v) i = v \/
    PArray.get (PArray.set t i v) i = PArray.get t i.
  move=> t i v; have [hin|hin] := boolP (i <? PArray.length t)%uint63.
    by left; rewrite get_setA.
  right; rewrite get_oobA ?default_setA; last by rewrite length_setA;
    apply: negbTE.
  by rewrite (@get_oobA _ _ (negbTE hin)).
rewrite /mkempty48.
apply: (@ifold_ind _ (fun a => PArray.get a c = PArray.make csize 0%uint63 \/
                               PArray.get a c = PArray.make 1%uint63 0%uint63));
    last by right; rewrite get_makeA.
move=> i b hb.
have [hic|hic] := eqVneq i c; last first.
  by rewrite get_set_otherA //; apply/eqP.
by rewrite -hic; case: (hset b i (PArray.make csize 0%uint63)) => ->;
   [left | rewrite hic].
Qed.

Lemma mkempty48P pg gr bt : mtest (mkempty48 tt) pg gr bt = false.
Proof.
rewrite /mtest /gget.
by case: (get_mkempty48 (Uint63.lsr (grpof pg gr) cshft)) => ->;
   rewrite get_makeE land0n.
Qed.

Lemma mempty48P pg gr bt : mtest mempty48 pg gr bt = false.
Proof. exact: mkempty48P. Qed.

(* a full map has every bit of every place in range                           *)
Lemma mfull48P m pg gr bt :
  mfull48 m -> inrange48 pg gr bt -> mtest m pg gr bt.
Proof.
move=> hf /and3P[hpg hgr hbt].
have h1 := iter_at hf (nltbP _ _ hpg).
have h2 := iter_at h1 (ltn_ngroupi hgr).
by rewrite /mtest (eqP h2) allbits48P.
Qed.

(* a bit set by a mark is the mark, or was there already                      *)
Lemma mmark48P m p g b pg gr bt :
  inrange48 p g b -> inrange48 pg gr bt ->
  mtest (mmark m p g b) pg gr bt ->
  [/\ p = pg, g = gr & b = bt] \/ mtest m pg gr bt.
Proof.
case/and3P => hp hg hb; case/and3P => hpg hgr hbt.
rewrite /mmark /gor /mtest.
case: (gget_gset m (grpof p g)
        (Uint63.lor (gget m (grpof p g)) (bitof b)) (grpof pg gr))
    => [->|[hgg ->]]; first by move=> hh; right.
move=> /test_lor/orP[hin|hnew]; first by right; rewrite -hgg.
left; have [-> ->] := grpof_inj (ltn_nclsi_npagei hp) hg
                                (ltn_nclsi_npagei hpg) hgr hgg.
by split => //; apply: bitof48_inj hnew.
Qed.

Section Pre48.

(* ---- the ten moves of H on cells of forty eight bits --------------------- *)

(* cpg is the corner PAIR table, 20160 * 10, where RowMap's mpg is the corner *)
(* permutation table, 40320 * 10.  cfl says whether the move is odd on the    *)
(* corners: if it is, the two halves of a cell change places, since the half  *)
(* is the corner parity.  It is one for U, U', D and D' and nought for the    *)
(* other six.                                                                 *)
(*                                                                            *)
(* The group table and the bit tables are RowMap's own and are read by        *)
(* RowMap's grpmv, once for each half.                                        *)

Variable cpg : arr.                 (* 20160 * 10                             *)
Variable cfl : arr.                 (* 10                                     *)
Variable mgr : arr.                 (* 20160 * 10                             *)
Variable msw : arr.                 (* 10                                     *)
Variable mlo mhi : arr.             (* 10 * 4096                              *)

Definition cpgmv (k pg : int) : int :=
  PArray.get cpg (Uint63.add (Uint63.mul pg nhi) k).

(* one cell, moved.  THE HIGH HALF IS MASKED TOO, for RowMap's reason: a bit  *)
(* above the forty eighth would index another move's block of the bit table.  *)
Definition grpmv48 (k v : int) : int :=
  let a := grpmv msw mlo mhi k (Uint63.land v allbits) in
  let b := grpmv msw mlo mhi k (Uint63.land (Uint63.lsr v nbiti) allbits) in
  if Uint63.eqb (PArray.get cfl k) 0%uint63
  then Uint63.lor a (Uint63.lsl b nbiti)
  else Uint63.lor b (Uint63.lsl a nbiti).

(* ---- one move over the whole map ----------------------------------------- *)

(* The source is read and the destination written, as in RowMap.v, and for    *)
(* the same reason: playing a move on what a move has just reached would      *)
(* count a member a level too soon.                                           *)
Definition prepmv48 (k : int) (src : rmap) (dst : rmap) : rmap :=
  ifold nclsn 0%uint63
    (fun pg d =>
       let pg' := cpgmv k pg in
       ifold ngroupn 0%uint63
         (fun gr d' =>
            let v := gget src (grpof pg gr) in
            if Uint63.eqb v 0%uint63 then d'
            else gor d' (grpof pg' (grmv mgr k gr)) (grpmv48 k v))
         d)
    dst.

(* the same move, also carrying the source across                            *)
Definition prepmv048 (k : int) (src : rmap) (dst : rmap) : rmap :=
  ifold nclsn 0%uint63
    (fun pg d =>
       let pg' := cpgmv k pg in
       ifold ngroupn 0%uint63
         (fun gr d' =>
            let g := grpof pg gr in
            let v := gget src g in
            if Uint63.eqb v 0%uint63 then d'
            else gor (gor d' g v) (grpof pg' (grmv mgr k gr)) (grpmv48 k v))
         d)
    dst.

(* the whole prepass, into the map it is given                               *)
Definition prepass48 (src dst : rmap) : rmap :=
  ifold nhn 0%uint63
    (fun k d =>
       if Uint63.eqb k 0%uint63 then prepmv048 k src d else prepmv48 k src d)
    dst.

End Pre48.

(* ---- three range facts the run asks for ---------------------------------- *)

(* A corner pair number is below the page count of RowMap.v, so its walks and *)
(* its grpof_inj apply to it unchanged.  These are the only bridges needed.   *)

Lemma nclsn_nwB : (nclsn < nwB)%N.
Proof. by rewrite nclsnE; exact: ngroupn_nwB. Qed.

Lemma ltn_nclsn_npagei pg : (to_nat pg < nclsn)%N -> (pg <? npagei)%uint63.
Proof.
move=> h; apply/nltbP; apply: leq_trans h _.
by rewrite nclsnE ngroupnE -/npagen npagenE.
Qed.

Lemma ltn_ngroupn_ngroupi gr : (to_nat gr < ngroupn)%N -> (gr <? ngroupi)%uint63.
Proof. by move=> h; apply/nltbP. Qed.
