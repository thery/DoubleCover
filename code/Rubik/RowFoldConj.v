(* =========================================================================  *)
(*  RowFoldConj.v -- the fold's tables really do conjugate the places.        *)
(* =========================================================================  *)

(* RowFoldPart.part_conj says a part conjugated by a renaming is the part of  *)
(* the conjugated places, and what it asks of the places is                   *)
(*                                                                            *)
(*     lperm t (v p) = u (lperm t p)                                          *)
(*                                                                            *)
(* This file asks that of the fold's own tables, by walking them.  The page   *)
(* is done here; the outer edges and the middle follow the same shape.        *)
(*                                                                            *)
(* EVERY INDEX IS AN int63, for the reason RowFoldSym gives: of_nat walks its *)
(* argument, and naming forty thousand pages in nat does not finish.  In      *)
(* int63 the sweep is five and a half seconds.                                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Sym16 Moves.
Require Import Row RowMap RowFold RowMemb RowFoldPart.
Require Import RowTabF RowFoldTab RowFoldSym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- the renaming, on the eight corner places ---------------------------- *)

(* lperm reads the place a table sends a place to, off the first slot.  The   *)
(* sixteen are worked out once, as values, so a sweep over forty thousand     *)
(* pages does not rebuild them.                                               *)
Definition lpc (s : nat) : seq nat := lperm cflatp 3 8 cposn (sy s).

Definition lpcs : seq (seq nat) := Eval vm_compute in [seq lpc s | s <- iota 0 16].

(* the renaming a page names, in Sym16's numbering *)
Notation psym w := (nth [::] lpcs (nth 0%N fren2sym (to_nat (fren w)))).

(* ---- and it does conjugate the page ------------------------------------- *)

(* For every one of the forty thousand pages: the KEPT page's permutation is  *)
(* the page's, conjugated by the renaming that folds it.  This is what        *)
(* part_conj asks, at u := the kept page and v := the page.                   *)
Definition pgconjC : bool :=
  iter npagen 0%uint63 (fun pg =>
     let w := PArray.get fpgi pg in
     let lp := psym w in
     let k := PArray.get fkeepi (fkpt w) in
     all (fun p => nth 0%N lp (up8 pg p) == up8 k (nth 0%N lp p)) (iota 0 8)).

Lemma pgconjCP : pgconjC. Proof. by vm_compute. Qed.

(* and the two ranges part_conj asks beside it: the places a renaming names,  *)
(* and the places a page's permutation names                                  *)
Definition lpcrngC : bool :=
  all (fun s => all (fun p => (nth 0%N (nth [::] lpcs s) p < 8)%N) (iota 0 8))
      (iota 0 16).

Lemma lpcrngCP : lpcrngC. Proof. by vm_compute. Qed.
