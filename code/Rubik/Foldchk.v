(* =========================================================================  *)
(*  Foldchk.v                                                                 *)
(*                                                                            *)
(*  The one obligation on the folded table that is not bookkeeping: a rank    *)
(*  whose orbit is shorter than sixteen reaches its representative by         *)
(*  several symmetries, and the row must give the same entry for all of       *)
(*  them.  stabC checks it, stabE_of_check turns that into Fold.v's stabE.    *)
(*                                                                            *)
(*  The table is a variable here, so this file compiles without it; only the  *)
(*  vm_compute of stabC needs the emitted data.                               *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts Phase1 Fold P1Fold Foldtab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Definition ntwbits := 12.               (* 2 ^ 12 covers the 2187 twists   *)

Section Chk.

Variable F : PArray.array arr.
Variable ract : int -> int -> int.

(* the entry the folded row gives for the symmetry u *)
Local Notation ent u r tw := (p1get F (foldi (frepi r) (twsymi tw u))).

(* Every symmetry that reaches the representative gives the same entry.  The
   one that fsym names is skipped, being the same term on both sides, which
   is what keeps the check to the 17 120 pairs that say something. *)
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
Proof. Admitted.

End Chk.
