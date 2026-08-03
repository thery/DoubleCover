(* =========================================================================  *)
(*  Farp1.v -- the three axis views, which is what rubik_par's heuristic is   *)
(*             the max over.                                                  *)
(*                                                                            *)
(*  ocaml/rubik_par.ml reads THREE lower bounds at each of THREE views and    *)
(*  takes the max of the nine.  The three views are {1, r, r ^ 2} for r the   *)
(*  120 degree rotation about a corner, which permutes the six faces in two   *)
(*  3-cycles.                                                                 *)
(*                                                                            *)
(*  THIS IS NOT Far.v's FIVE VIEWS.  Far.v conjugates by {1, Sy, Sx, SySx,    *)
(*  SxSy} for its flip x slice search.  The two sets are different and must   *)
(*  not be mixed: the node counts that make bench/p1gen.ml a node for node    *)
(*  reference for rubik_par are the three axis ones.                          *)
(*                                                                            *)
(*  WHICH rotation it is was DERIVED, not transcribed: bench/p1gen.ml `views' *)
(*  searches the 48 symmetries for an order 3 element whose conjugation       *)
(*  permutes the move set, and prints it as the table below together with the *)
(*  two move relabellings.  Its own check reports 0 mismatches of 36, and     *)
(*  rot3_relabel reproduces that check here.  Same rule as the corner data in *)
(*  Phase1.v: derive, do not transcribe.                                      *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts Phase1 Far.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- 1. The rotation, and what conjugation by it does to the moves ------- *)

Definition rot3t : seq nat :=
  [:: 21; 19; 16; 22; 17; 23; 20; 18; 40; 41; 42; 43; 44; 45; 46; 47;
      29; 27; 24; 30; 25; 31; 28; 26; 7; 6; 5; 4; 3; 2; 1; 0;
      10; 12; 15; 9; 14; 8; 11; 13; 37; 35; 32; 38; 33; 39; 36; 34]%N.

(* the move relabellings: conjugating by r sends move k to move mv3a k, and
   by r ^ 2 to move mv3b k *)
Definition mv3a : seq nat :=
  [:: 6; 7; 8; 0; 1; 2; 3; 4; 5; 15; 16; 17; 9; 10; 11; 12; 13; 14]%N.

Definition mv3b : seq nat :=
  [:: 3; 4; 5; 6; 7; 8; 0; 1; 2; 12; 13; 14; 15; 16; 17; 9; 10; 11]%N.

Definition rot3t2 : seq nat := comp_tab rot3t rot3t.

Lemma rot3t_ok : tab_ok 47 rot3t.
Proof. by vm_compute. Qed.

Lemma rot3t2_ok : tab_ok 47 rot3t2.
Proof. by vm_compute. Qed.

(* it really is an order 3 element *)
Lemma rot3t_order3 : comp_tab rot3t rot3t2 = id_tab 47.
Proof. by vm_compute. Qed.

(* it keeps cubies together, which every view has to *)
Lemma cubt_rot3 : cubt rot3t.
Proof. by vm_compute. Qed.

Lemma cubt_rot3t2 : cubt rot3t2.
Proof. by vm_compute. Qed.

(* THE FACT EVERYTHING RESTS ON, and the same one p1gen checks in OCaml:
   conjugation by each view permutes the move set, by the relabelling. *)
Lemma rot3_relabel :
  all (fun k => (conjt rot3t (nth [::] mtabs k) == nth [::] mtabs (nth 0%N mv3a k))
             && (conjt rot3t2 (nth [::] mtabs k) == nth [::] mtabs (nth 0%N mv3b k)))
      (iota 0 18).
Proof. by vm_compute. Qed.

(* so each view sends a move to a move -- Far.v's view_move, for these views *)
Lemma size_mtabs18 : seq.size mtabs = 18%N.
Proof. by vm_compute. Qed.

(* the relabellings land in range, so the conjugated move is a move *)
Lemma mv3a_lt : all (fun k => (nth 0%N mv3a k < 18)%N) (iota 0 18).
Proof. by vm_compute. Qed.

Lemma mv3b_lt : all (fun k => (nth 0%N mv3b k < 18)%N) (iota 0 18).
Proof. by vm_compute. Qed.

Lemma rot3_move k : (k < 18)%N -> conjt rot3t (nth [::] mtabs k) \in mtabs.
Proof.
move=> kL; have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have /andP[/eqP -> _] := allP rot3_relabel _ kM.
by apply: mem_nth; rewrite size_mtabs18; exact: (allP mv3a_lt _ kM).
Qed.

Lemma rot3t2_move k : (k < 18)%N -> conjt rot3t2 (nth [::] mtabs k) \in mtabs.
Proof.
move=> kL; have kM : k \in iota 0 18 by rewrite mem_iota add0n leq0n kL.
have /andP[_ /eqP ->] := allP rot3_relabel _ kM.
by apply: mem_nth; rewrite size_mtabs18; exact: (allP mv3b_lt _ kM).
Qed.

(* and Far.v's sigma -- the index of the conjugated move -- is the
   relabelling, so every lemma Far.v states in terms of sigma applies *)
Lemma sigma_rot3a : all (fun k => sigma rot3t k == nth 0%N mv3a k) (iota 0 18).
Proof. by vm_compute. Qed.

Lemma sigma_rot3b : all (fun k => sigma rot3t2 k == nth 0%N mv3b k) (iota 0 18).
Proof. by vm_compute. Qed.

(* ---- 2. Conjugation as an array operation -------------------------------- *)

(* the same shape as Far.v's conjy / conjx: the conjugating tables are closed
   literals so the VM shares them, and the bracketing is ri . (a . r) to match
   conji. *)
Definition r3ti     : arr := Eval vm_compute in t2ti 47 rot3t.
Definition r3ti_inv : arr := Eval vm_compute in inv_tabi 47 r3ti.

Definition conj3 (a : arr) : arr :=
  comp_tabi 47 r3ti_inv (comp_tabi 47 a r3ti).

Lemma r3ti_ok : tabi_ok 47 r3ti.
Proof. by vm_compute. Qed.

Lemma conj3E a : conj3 a = conji rot3t a.
Proof. by rewrite /conj3 /conji; congr (comp_tabi _ _ (comp_tabi _ _ _)). Qed.
