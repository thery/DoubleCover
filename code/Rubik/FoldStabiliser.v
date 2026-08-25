(* =========================================================================  *)
(*  FoldStabiliser.v -- Short orbits: every symmetry reaching the             *)
(*     representative agrees.                                                 *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts Phase1 Fold P1Fold FoldTables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Definition ntwbits := 12.               (* 2 ^ 12 covers the 2187 twists      *)

Section Chk.

Variable F : PArray.array arr.
Variable ract : int -> int -> int.

(* the entry the folded row gives for the symmetry u                          *)
Local Notation ent u r tw := (p1getd F (foldi (frepi r) (twsymi tw u))).

(* Every symmetry that reaches the representative gives the same entry.  The  *)
(* one that fsym names is skipped, being the same term on both sides, which   *)
(* is what keeps the check to the 17 120 pairs that say something.            *)
Definition stabC : bool :=
  all_powi nrbits 0%uint63 (Uint63.lsl 1 (of_nat nrbits))
    (fun r =>
       if (nfsi <=? r)%uint63 then true
       else all (fun u =>
              let ui := of_nat u in
              if (ui =? fsymi r)%uint63 then true
              else if (ract r ui =? repsi (frepi r))%uint63 then
                all_powi ntwbits 0%uint63 (Uint63.lsl 1 (of_nat ntwbits))
                  (fun tw =>
                     if (ntwisti <=? tw)%uint63 then true
                     else (ent ui r tw =? ent (fsymi r) r tw)%uint63)
              else true)
            (iota 0 16)).

Lemma stabCE : stabC =
  all_powi nrbits 0%uint63 (Uint63.lsl 1 (of_nat nrbits))
    (fun r =>
       if (nfsi <=? r)%uint63 then true
       else all (fun u =>
              let ui := of_nat u in
              if (ui =? fsymi r)%uint63 then true
              else if (ract r ui =? repsi (frepi r))%uint63 then
                all_powi ntwbits 0%uint63 (Uint63.lsl 1 (of_nat ntwbits))
                  (fun tw =>
                     if (ntwisti <=? tw)%uint63 then true
                     else (ent ui r tw =? ent (fsymi r) r tw)%uint63)
              else true)
            (iota 0 16)).
Proof. by []. Qed.

Lemma stabE_of_check tw r u :
  stabC -> (r <? nfsi)%uint63 -> (to_nat u < 16)%N ->
  (to_nat tw < ntwist)%N -> ract r u = repsi (frepi r) ->
  ent u r tw = ent (fsymi r) r tw.
Proof.
move=> hchk rL uL twL hu.
(* the symmetry fsym names is the same term on both sides                     *)
case: (boolP (u =? fsymi r)%uint63) => [/eqb_correct ->|hne] //.
have hrlt : (to_nat r < 2 ^ nrbits)%N.
  by apply: leq_trans (_ : to_nat nfsi <= _); [apply/nltbP | vm_compute].
(* the outer loop as all_pow, the two inner ones left as written: turning     *)
(* them all at once puts a rewrite under a binder and does not come back      *)
have hall : all_pow nrbits 0%uint63
  (fun r0 => if (nfsi <=? r0)%uint63 then true
             else all (fun u0 => let ui := of_nat u0 in
                    if (ui =? fsymi r0)%uint63 then true
                    else if (ract r0 ui =? repsi (frepi r0))%uint63 then
                      all_powi ntwbits 0%uint63 (Uint63.lsl 1 (of_nat ntwbits))
                        (fun tw0 => if (ntwisti <=? tw0)%uint63 then true
                                    else (ent ui r0 tw0 =?
                                          ent (fsymi r0) r0 tw0)%uint63)
                    else true)
                  (iota 0 16)).
  rewrite -all_powiE; last by vm_compute.
  (* -stabCE folds the body back to the name; exact: hchk alone would         *)
  (* unify by evaluating the loop                                             *)
  rewrite -stabCE; exact: hchk.
(* peel the rank loop                                                         *)
have hr := all_powP (k := nrbits) _ hall hrlt.
have hg : (nfsi <=? r)%uint63 = false.
  by apply: negbTE; apply/negP => /nlebP; rewrite leqNgt (elimT (nltbP _ _) rL).
rewrite hg in hr.
move: hr => /(_ isT) hr.
(* peel the sixteen symmetries                                                *)
have hmem : to_nat u \in iota 0 16 by rewrite mem_iota /=.
have htw := allP hr _ hmem.
rewrite to_natK in htw.
cbv zeta in htw.
rewrite (negPf hne) hu Uint63.eqb_refl in htw.
(* peel the twist loop                                                        *)
rewrite all_powiE in htw; last by vm_compute.
have htlt : (to_nat tw < 2 ^ ntwbits)%N by apply: leq_trans twL _; vm_compute.
have h2 := all_powP (k := ntwbits) _ htw htlt.
have hg2 : (ntwisti <=? tw)%uint63 = false.
  by apply: negbTE; apply/negP => /nlebP; rewrite leqNgt twL.
rewrite hg2 in h2.
by apply/eqb_correct/h2.
Qed.

End Chk.
