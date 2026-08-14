(* =========================================================================  *)
(*  Fsparity.v -- What makes a packed value a genuine flip x slice summary,   *)
(*     and why a move preserves it.                                           *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Tabi Coordfsi Fstab Moves Phase1 Far.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- 3bis.  What makes a packed value a genuine summary ------------------ *)

(* THE GUARD `fsidx x <? nfsi' IS NOT ENOUGH, AND THE THREE CERTIFICATES OF   *)
(* SECTION 5 WERE FALSE WITH IT.  Two packed values can share a rank without  *)
(* moving alike, for two separate reasons:                                    *)
(*                                                                            *)
(* - srank returns nsrank = 495 both for a twelve bit mask WITHOUT four bits  *)
(*   set and as the array default, so for those fsidx x = (f + 1) * 495 --    *)
(*   which is BELOW nfsi = 2048 * 495 for every f < 2047.  COUNTED: 495 of    *)
(*   the 4096 masks are genuine and 3601 are not, so the old guard admits     *)
(*   8 385 007 of the 2 ^ 24 rather than the 1 013 760 summaries.  The        *)
(*   comment claiming it "leaves only the 6 %" was wrong by 8.3x.             *)
(*                                                                            *)
(* - fsidx masks the flip with 2047, not 4095, because bit 11 is the parity   *)
(*   of the other eleven for a real cube -- Phase1.v says exactly that where  *)
(*   fsidx is defined.  But actf moves all twelve bits.  MEASURED: at         *)
(*   c0 = coordt (id_tab 47) and c1 = c0 lxor 2048, fsidx c0 = fsidx c1, yet  *)
(*   after the fourth move the two ranks are 300 and 8220.                    *)
(*                                                                            *)
(* fsok asks for both, and admits exactly nflip * nsrank = nfs values -- the  *)
(* count the emitted tables have a row for.  Fixing it is therefore a         *)
(* soundness fix AND the largest saving available on the certificate.         *)

(* fpar, sok and fsok, and everything provable about them at the PERMUTATION  *)
(* level, are in Phase1.v: p1stepF there needs the guard, and twcP there      *)
(* carries the parity.  What is left here is the array level, which Phase1.v  *)
(* cannot state -- it does not know about comp_tabi or mtis.                  *)

(* the old bound, where the old bound is what is wanted                       *)
Lemma fsok_lt x : fsok x -> (fsidx x <? nfsi)%uint63.
Proof.
move=> /andP[hs _]; apply: fsidx_ltB.
by have := nltbP _ _ hs; rewrite (_ : to_nat nsranki = nsrank) //; vm_compute.
Qed.

(* THE INVARIANT, at the int level: a move does not change the flip parity    *)
Lemma fpar_actf x mt : mt \in mtabs ->
  fpar (actf x (mdatf_of_tab mt)) = fpar x.
Proof.
move=> hmt; rewrite actfE.
have /andP[hp hx] := allP mtabs_fparP _ hmt.
(* @: Unset Strict Implicit makes d implicit, and hp fixes only d.1           *)
rewrite (@fpar_actd x (mdat_of_tab mt) hp).
  by move: hx; rewrite mdat_snd; case: odd => //=; rewrite addbF.
by rewrite mdat_snd /mxbit size_map size_iota.
Qed.

(* and the parity at the array level: a move does not change it               *)
Lemma fpar_step a k : tabi_ok 47 a -> cubti a -> (k < 18)%N ->
  fpar (coordi (comp_tabi 47 a (nth (id_tabi 47) mtis k))) = fpar (coordi a).
Proof.
move=> aok ca kL.
have kL' : (k < seq.size mtis)%N by rewrite size_mtis.
rewrite (actcdE kL' aok ca) /actcd.
have -> : nth (mdatf_of_tab [::]) mdatafd k = mdatf_of_tab (nth [::] mtabs k).
  by rewrite mdatafdE /mdataf (nth_map [::]) // size_mtabs18.
by apply: fpar_actf; rewrite mem_nth // size_mtabs18.
Qed.

