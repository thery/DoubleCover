(* =========================================================================  *)
(*  HRoot.v -- Reid's six positions, as facelet tables, and the three views.  *)
(* =========================================================================  *)

(* The quarter-turn lower bound searches six positions, each of them the      *)
(* superflip composed with fourspot and then with a short prefix.  This file  *)
(* builds those six from the words, on the tables of Moves.v, and relabels    *)
(* them for the three axes the table is read along.  It computes; it proves   *)
(* nothing yet.                                                               *)
(*                                                                            *)
(* ocaml/rubik_h.ml is the specification, and the check that the two agree is *)
(* sfw_sfti below: the twenty-move word must come out as the superflip that   *)
(* Moves.v already knows.                                                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* the last facelet, so a table has 48 entries                                *)
Definition flast := 47.

(* the twelve quarter turns, and the six faces                                *)
Definition nqt := 12.
Definition nface := 6.

Definition idi : arr := id_tabi flast.

Definition mvi (k : nat) : arr := nth idi mtis k.

(* a word, applied to a table, oldest move first                              *)
Definition appw (a : arr) (w : seq nat) : arr :=
  foldl (fun x k => comp_tabi flast x (mvi k)) a w.

(* ---- the twelve quarter turns among the eighteen moves ------------------- *)

(* Turn m turns face m %/ 2, clockwise when m is even.  The eighteen moves    *)
(* are a face, then its square, then its inverse, so the quarter turns are    *)
(* the indices 3 f and 3 f + 2.                                               *)
Definition qt18 (m : nat) : nat := 3 * (m %/ 2) + (if odd m then 2 else 0).

Definition qtw (w : seq nat) : seq nat := [seq qt18 m | m <- w].

(* ---- the superflip, and fourspot ----------------------------------------  *)

(* U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2                         *)
Definition sfw : seq nat :=
  [:: 0; 4; 6; 15; 3; 16; 3; 1; 12; 16; 3; 2; 11; 4; 6; 5; 12; 16; 1; 7]%N.

(* F2 B2 U D' R2 L2 U D'                                                      *)
Definition fsw : seq nat := [:: 7; 16; 0; 11; 4; 13; 0; 11]%N.

(* THE CHECK ON THE WHOLE ENCODING.  The word has to give the superflip that  *)
(* Moves.v built from its cycles, so the move order, the powers and the way a *)
(* word is composed are all tested at once.                                   *)
Lemma sfw_sfti : eq_tabi flast (appw idi sfw) sfti = true.
Proof. by vm_compute. Qed.

(* superflip composed with fourspot, which is Reid's position                 *)
Definition targeti : arr := appw idi (sfw ++ fsw).

(* ---- the six prefixes --------------------------------------------------   *)

(* Proposition 2 of doc/reid-1998-fourspot.md: every maneuver for the         *)
(* position can be turned into one that begins with one of six sequences.     *)
(* They are quarter turns:  R U,  R' U D,  R' U F',  R' U R',  R' U B',       *)
(* R' U L'.                                                                   *)
Definition pfxs : seq (seq nat) :=
  [:: [:: 2; 0]; [:: 3; 0; 6]; [:: 3; 0; 5];
      [:: 3; 0; 3]; [:: 3; 0; 11]; [:: 3; 0; 9] ]%N.

Definition npfx := seq.size pfxs.

Definition rooti (k : nat) : arr := appw targeti (qtw (nth [::] pfxs k)).

(* Reid searched the first prefix through 22 quarter turns and the other five *)
(* through 21, which with the prefix is 24 in every case.                     *)
Definition rootd (k : nat) : nat := 24 - seq.size (nth [::] pfxs k).

(* ---- the three viewing angles -------------------------------------------  *)

(* The table is built around the up-down axis, so it answers for that axis    *)
(* alone.  Turning the whole cube gives another axis, and every answer is a   *)
(* lower bound on the same distance.  A rotation only relabels the faces, so  *)
(* the turned position is the relabelled WORD.                                *)
(*                                                                            *)
(* Faces are U R F D L B.  The second line turns the cube about the front-    *)
(* back axis, U -> R -> D -> L -> U; the third about the right-left axis,     *)
(* U -> F -> D -> B -> U.  Both are rotations, so clockwise stays clockwise.  *)
Definition nax := 3.

Definition axes : seq (seq nat) :=
  [:: [:: 0; 1; 2; 3; 4; 5]; [:: 1; 3; 2; 4; 0; 5]; [:: 2; 1; 3; 5; 4; 0] ]%N.

Definition axf (i f : nat) : nat := nth 0 (nth [::] axes i) f.

(* the same relabelling on the twelve quarter turns and on the eighteen       *)
Definition cmv (i m : nat) : nat := 2 * axf i (m %/ 2) + odd m.
Definition cmv18 (i m : nat) : nat := 3 * axf i (m %/ 3) + m %% 3.

(* the position of the k-th prefix, seen along axis i                         *)
Definition rooti_ax (i k : nat) : arr :=
  appw (appw idi [seq cmv18 i m | m <- sfw ++ fsw])
       (qtw [seq cmv i m | m <- nth [::] pfxs k]).

(* Axis 0 is the identity relabelling, so it must give the position itself.   *)
Lemma rooti_ax0 : all (fun k => eq_tabi flast (rooti_ax 0 k) (rooti k))
                      (iota 0 npfx) = true.
Proof. by vm_compute. Qed.

(* A view is sound because the relabelling is a rotation, and a rotation      *)
(* keeps a position's distance from solved.  What is checked here is the      *)
(* first half of that: opposite faces stay opposite, which is what makes the  *)
(* relabelling a symmetry of the cube at all.  Faces are three apart from     *)
(* their opposites.                                                           *)
Definition oppf (f : nat) : nat := (f + 3) %% nface.

Definition axis_opp (i : nat) : bool :=
  all (fun f => axf i (oppf f) == oppf (axf i f)) (iota 0 nface).

Lemma axes_opp : all axis_opp (iota 0 nax) = true.
Proof. by vm_compute. Qed.
