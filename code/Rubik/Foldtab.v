(* =========================================================================  *)
(*  Foldtab.v                                                                 *)
(*                                                                            *)
(*  The folding tables, read.  P1Fold.v holds them packed; this file unpacks  *)
(*  each one and bounds it, which is what Fold.v asks of its variables.       *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts Phase1 Fold P1Fold.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the widths the generator packs with -------------------------------- *)

Definition nsymi   : int := 16%uint63.                 (* nsym            *)
Definition nrbits  := 20.                (* 2 ^ 20 covers the ranks       *)
Definition nwide   : int := 3%uint63.       (* twenty bit values a word    *)
Definition wbits   : int := 20%uint63.
Definition wmaski  : int := 1048575%uint63.            (* 2 ^ 20 - 1      *)
Definition nnarrow : int := 15%uint63.        (* four bit values a word    *)
Definition nbits   : int := 4%uint63.
Definition nmask4  : int := 15%uint63.

(* a twenty bit value out of a flat array, three to a word *)
Definition get20 (a : arr) (i : int) : int :=
  let w := Uint63.div i nwide in
  let j := Uint63.sub i (Uint63.mul w nwide) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j wbits)) wmaski.

(* a four bit value out of a flat array, fifteen to a word *)
Definition get4 (a : arr) (i : int) : int :=
  let w := Uint63.div i nnarrow in
  let j := Uint63.sub i (Uint63.mul w nnarrow) in
  Uint63.land (Uint63.lsr (PArray.get a w) (Uint63.mul j nbits)) nmask4.

(* ---- the four tables ----------------------------------------------------- *)

Definition repa : arr := Eval vm_compute in rep_data.
Definition syma : arr := Eval vm_compute in sym_data.
Definition twsyma : arr := Eval vm_compute in twsym_data.
Definition repsa : arr := Eval vm_compute in reps_data.

(* the orbit of a rank *)
Definition frepi (r : int) : int := get20 repa r.

(* a symmetry taking that rank to its orbit's representative *)
Definition fsymi (r : int) : int := get4 syma r.

(* the twist under a symmetry *)
Definition twsymi (tw s : int) : int :=
  get20 twsyma (Uint63.add (Uint63.mul tw nsymi) s).

(* the rank of an orbit's representative *)
Definition repsi (i : int) : int := get20 repsa i.

(* ---- and the bounds Fold.v asks for -------------------------------------- *)

(* every orbit index is below norbi *)
Definition frepC : bool :=
  all_powi nrbits 0%uint63 (Uint63.lsl 1 (of_nat nrbits))
           (fun r => if (nfsi <=? r)%uint63 then true
                     else (frepi r <? norbi)%uint63).

Lemma frepCP : frepC. Proof. by vm_compute. Qed.

Lemma frepCE : frepC =
  all_powi nrbits 0%uint63 (Uint63.lsl 1 (of_nat nrbits))
           (fun r => if (nfsi <=? r)%uint63 then true
                     else (frepi r <? norbi)%uint63).
Proof. by []. Qed.

Lemma frepL r : (r <? nfsi)%uint63 -> (frepi r <? norbi)%uint63.
Proof.
move=> hr.
have h1 : (to_nat r < to_nat nfsi)%N by apply/nltbP.
have hlt : (to_nat r < 2 ^ nrbits)%N.
  by apply: leq_trans h1 _; vm_compute.
have hall : all_pow nrbits 0%uint63
              (fun r0 => if (nfsi <=? r0)%uint63 then true
                         else (frepi r0 <? norbi)%uint63).
  by rewrite -all_powiE //; rewrite -frepCE; exact: frepCP.
have := all_powP (k := nrbits) _ hall hlt.
have -> : (nfsi <=? r)%uint63 = false.
  by apply: negbTE; apply/negP => /nlebP; rewrite leqNgt h1.
by apply; vm_compute.
Qed.

(* every symmetry index is below sixteen *)
Definition fsymC : bool :=
  all_powi nrbits 0%uint63 (Uint63.lsl 1 (of_nat nrbits))
           (fun r => if (nfsi <=? r)%uint63 then true
                     else (fsymi r <? nsymi)%uint63).

Lemma fsymCP : fsymC. Proof. by vm_compute. Qed.
