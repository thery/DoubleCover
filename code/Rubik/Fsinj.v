(* =========================================================================  *)
(*  Fsinj.v -- the flip and slice index is one to one where it is used.       *)
(* =========================================================================  *)

(* WHY.  RowInst's leaf test asks three questions where one would do: whether *)
(* the coordinate is the solved one, and then, of the forty eight entry cube, *)
(* whether the twist is nought and the flip and slice rank right.  Its own    *)
(* comment says why the last two are there -- "the coordinate is packed and   *)
(* unpacking it is not proved one to one".                                    *)
(*                                                                            *)
(* MEASURED, depth twelve, the same tree: with the three questions the search *)
(* is 37.9 s and with the first alone 18.5.  THE TWO EXTRA QUESTIONS ARE HALF *)
(* THE SEARCH, and they recompute a number the search already carries.        *)
(*                                                                            *)
(* WHAT IS PROVED HERE.  fsidx is the flip times 495 plus the rank of the     *)
(* slice mask, so it is one to one exactly when those two halves are.  The    *)
(* mask half is asked of the table: its inverse is built from it and the 4096 *)
(* masks are checked by computation.  The flip half is eleven bits, and the   *)
(* twelfth is the parity of the other eleven for a real cube -- which is what *)
(* a position carries anyway -- so a flip with eleven nought bits and even    *)
(* parity is nought, and that is the other 4096 check.                        *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1 RowMap.

Notation arr := (PArray.array int).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- the index taken apart ----------------------------------------------- *)

Lemma to_nat_nsranki : to_nat nsranki = nsrank.
Proof. by vm_compute. Qed.

Lemma nfs_lt : (nflip * nsrank < nwB)%N.
Proof.
apply: leq_ltn_trans (_ : (2 ^ 20)%N < _); first by vm_compute.
by rewrite nwB_pow ltn_exp2l.
Qed.

Lemma fsidxE x :
  (to_nat (PArray.get srank (Uint63.lsr x 12%uint63)) < nsrank)%N ->
  to_nat (fsidx x)
  = (to_nat (Uint63.land x 2047%uint63) * nsrank
     + to_nat (PArray.get srank (Uint63.lsr x 12%uint63)))%N.
Proof.
move=> hs; rewrite /fsidx.
have hf : (to_nat (Uint63.land x 2047%uint63) < nflip)%N.
  rewrite landC -(_ : (2 ^ 11 = nflip)%N); last by vm_compute.
  by apply: to_nat_land_bound; vm_compute.
have hmulb : (to_nat (Uint63.land x 2047%uint63) * to_nat nsranki < nwB)%N.
  rewrite to_nat_nsranki; apply: leq_ltn_trans nfs_lt.
  by rewrite leq_mul2r; apply/orP; right; exact: ltnW hf.
have hmul : to_nat (Uint63.mul (Uint63.land x 2047%uint63) nsranki)
          = (to_nat (Uint63.land x 2047%uint63) * nsrank)%N.
  by rewrite (to_nat_mul _ _ hmulb) to_nat_nsranki.
have hs1 : (to_nat (Uint63.land x 2047%uint63) * nsrank
            + to_nat (PArray.get srank (Uint63.lsr x 12%uint63))
            <= (to_nat (Uint63.land x 2047%uint63)).+1 * nsrank)%N.
  by rewrite mulSn addnC leq_add2r; apply: ltnW.
have hs2 : ((to_nat (Uint63.land x 2047%uint63)).+1 * nsrank
            <= nflip * nsrank)%N.
  by rewrite leq_mul2r hf orbT.
have haddb : (to_nat (Uint63.mul (Uint63.land x 2047%uint63) nsranki)
              + to_nat (PArray.get srank (Uint63.lsr x 12%uint63)) < nwB)%N.
  by rewrite hmul; apply: leq_ltn_trans nfs_lt; apply: leq_trans hs1 hs2.
by rewrite (to_nat_add _ _ haddb) hmul.
Qed.

(* ---- the rank of a mask is one to one ------------------------------------ *)

(* The inverse table, built from srank itself by writing each mask at its own *)
(* rank.  A mask that is not four bits gets 495, which is past the end, and a *)
(* write past the end does nothing -- so only the real masks land in it.      *)
Definition sunrank : arr :=
  Eval vm_compute in
  ifold nmask 0%uint63
        (fun m a => PArray.set a (PArray.get srank m) m)
        (PArray.make nsranki 0%uint63).

Definition sunrankC : bool :=
  all (fun m => (PArray.get srank (of_nat m) <? nsranki)%uint63
                ==> (PArray.get sunrank (PArray.get srank (of_nat m))
                     == of_nat m))
      (iota 0 nmask).

Lemma sunrankCP : sunrankC. Proof. by vm_compute. Qed.

Lemma srank_back m : (to_nat m < nmask)%N ->
  (PArray.get srank m <? nsranki)%uint63 ->
  PArray.get sunrank (PArray.get srank m) = m.
Proof.
move=> hm hs; have := sunrankCP; rewrite /sunrankC.
move=> /allP /(_ (to_nat m)); rewrite mem_iota add0n leq0n hm => /(_ isT).
by rewrite to_natK => /implyP /(_ hs) /eqP.
Qed.

(* ---- the twelfth flip is the parity of the other eleven ------------------ *)

Definition flow0C : bool :=
  all (fun m => ((Uint63.land (of_nat m) 2047%uint63 == 0%uint63)
                 && ~~ fpar (of_nat m))
                ==> (of_nat m == 0%uint63))
      (iota 0 nmask).

Lemma flow0CP : flow0C. Proof. by vm_compute. Qed.

Lemma flow0 u : (to_nat u < nmask)%N -> Uint63.land u 2047%uint63 = 0%uint63 ->
  ~~ fpar u -> u = 0%uint63.
Proof.
move=> hu h1 h2; have := flow0CP; rewrite /flow0C.
move=> /allP /(_ (to_nat u)); rewrite mem_iota add0n leq0n hu => /(_ isT).
by rewrite to_natK h1 h2 eqxx => /implyP /(_ isT) /eqP.
Qed.

(* ---- and the whole of it ------------------------------------------------- *)

(* THE TWO FACTS ABOUT THE SOLVED SUMMARY ARE ASKED FOR, not computed: this  *)
(* file never mentions a permutation to an evaluator.  RowInst hands them     *)
(* over, where coordfs 1 is a number it has already worked out.               *)
Lemma coordfs_solved g : cubP g -> ~~ fpar (coordfs g) ->
  Uint63.land (coordfs 1) 2047%uint63 = 0%uint63 ->
  Uint63.land (coordfs 1) 4095%uint63 = 0%uint63 ->
  fsidx (coordfs g) = fsidx (coordfs 1) -> coordfs g = coordfs 1.
Proof.
move=> cg hp hY0 hY12 heq.
have hsX : (to_nat (PArray.get srank
              (Uint63.lsr (coordfs g) 12%uint63)) < nsrank)%N.
  by rewrite -to_nat_nsranki; apply/nltbP; exact: sok_coordfs.
have hsY : (to_nat (PArray.get srank
              (Uint63.lsr (coordfs 1) 12%uint63)) < nsrank)%N.
  by rewrite -to_nat_nsranki; apply/nltbP; apply: sok_coordfs; exact: cubP1.
have he : (to_nat (Uint63.land (coordfs g) 2047%uint63) * nsrank
           + to_nat (PArray.get srank (Uint63.lsr (coordfs g) 12%uint63))
         = to_nat (Uint63.land (coordfs 1) 2047%uint63) * nsrank
           + to_nat (PArray.get srank (Uint63.lsr (coordfs 1) 12%uint63)))%N.
  exact: (eq_trans (eq_trans (esym (fsidxE hsX)) (f_equal (fun z : int => to_nat z) heq))
                   (fsidxE hsY)).
rewrite hY0 (_ : to_nat 0%uint63 = 0%N) // mul0n add0n in he.
have hf0 : to_nat (Uint63.land (coordfs g) 2047%uint63) = 0%N.
  apply/eqP; rewrite -leqn0 leqNgt; apply/negP => h1.
  have h2 : (nsrank <= to_nat (Uint63.land (coordfs g) 2047%uint63) * nsrank)%N.
    by apply: leq_pmull.
  move: hsY; rewrite -he ltnNge => /negP; apply.
  by apply: leq_trans h2 (leq_addr _ _).
have hse : PArray.get srank (Uint63.lsr (coordfs g) 12%uint63)
         = PArray.get srank (Uint63.lsr (coordfs 1) 12%uint63).
  by apply: to_nat_inj; move: he; rewrite hf0 mul0n add0n.
have hmm : Uint63.lsr (coordfs g) 12%uint63 = Uint63.lsr (coordfs 1) 12%uint63.
  rewrite -(srank_back (smask_lt g) (sok_coordfs cg)).
  by rewrite -(srank_back (smask_lt 1) (sok_coordfs cubP1)) hse.
have hlow u : (to_nat (Uint63.land u 4095%uint63) < nmask)%N.
  rewrite landC -(_ : (2 ^ 12 = nmask)%N); last by vm_compute.
  by apply: to_nat_land_bound; vm_compute.
have hX12 : Uint63.land (coordfs g) 4095%uint63 = 0%uint63.
  apply: flow0 => //; last by rewrite landC fpar_mask.
  rewrite -landA (_ : Uint63.land 4095%uint63 2047%uint63 = 2047%uint63) //.
  by apply: to_nat_inj; rewrite hf0.
have hland u : Uint63.land u 4095%uint63 = Uint63.mod u 4096%uint63.
  rewrite -[4095%uint63]/(decr (Uint63.lsl 1 12))%uint63.
  rewrite -[4096%uint63]/(Uint63.lsl 1 12)%uint63.
  by apply: land_power2; vm_compute.
have hd u : to_nat u = (to_nat (Uint63.lsr u 12%uint63) * 4096
                        + to_nat (Uint63.land u 4095%uint63))%N.
  rewrite to_nat_lsr hland to_nat_mod.
  rewrite (_ : to_nat 12%uint63 = 12%N) // (_ : to_nat 4096%uint63 = 4096%N) //.
  by rewrite (_ : (2 ^ 12 = 4096)%N) // -divn_eq.
apply: to_nat_inj.
by rewrite [LHS]hd [RHS]hd hmm hX12 hY12.
Qed.
