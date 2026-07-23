(* ========================================================================= *)
(*  Rubik333.v                                                               *)
(*                                                                           *)
(*  A group-theoretic representation of the 3x3x3 Rubik's cube, in the       *)
(*  style of Rokicki, Kociemba, Davidson, Dethridge, "The diameter of the    *)
(*  Rubik's cube group is twenty" (SIAM J. Discrete Math., 2013).            *)
(*                                                                           *)
(*  We use the FACELET model (the paper's defining model, p.1088):           *)
(*    G = <S> acting on the 48 non-center stickers.                          *)
(*  Facelets are numbered 0..47 following the standard (Wikipedia/GAP)        *)
(*  numbering, minus 1 to be 0-based.                                        *)
(*                                                                           *)
(*  Generic material lives elsewhere: cyclic permutations in Cyc.v, the word  *)
(*  metric / balls in Ball.v.                                                *)
(*                                                                           *)
(*  NOTE ON COMPUTATION.  Cardinalities such as |G| = 43252003274489856000   *)
(*  and |H| = 19508428800, and any check requiring evaluation of a           *)
(*  {perm 'I_48} (these do not reduce in reasonable time under vm_compute),  *)
(*  are stated as lemmas and left Admitted with the tag [COMPUTATION].       *)
(*  This mirrors the paper: the reduction is a proof; the numeric facts are  *)
(*  external computations.                                                   *)
(* ========================================================================= *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- 1. Facelets --------------------------------------------------------- *)

Definition facelet := 'I_48.

Local Notation "n '@'" := (inord n : facelet) (at level 2, format "n '@'").

(* ---- 2. The six clockwise quarter turns ---------------------------------- *)
(* Cycles are the standard generators (0-based).                             *)

Definition Umove : {perm facelet} :=
  cyc [:: 0@; 2@; 7@; 5@] * cyc [:: 1@; 4@; 6@; 3@] *
  cyc [:: 8@; 32@; 24@; 16@] * cyc [:: 9@; 33@; 25@; 17@] *
  cyc [:: 10@; 34@; 26@; 18@].

Definition Lmove : {perm facelet} :=
  cyc [:: 8@; 10@; 15@; 13@] * cyc [:: 9@; 12@; 14@; 11@] *
  cyc [:: 0@; 16@; 40@; 39@] * cyc [:: 3@; 19@; 43@; 36@] *
  cyc [:: 5@; 21@; 45@; 34@].

Definition Fmove : {perm facelet} :=
  cyc [:: 16@; 18@; 23@; 21@] * cyc [:: 17@; 20@; 22@; 19@] *
  cyc [:: 5@; 24@; 42@; 15@] * cyc [:: 6@; 27@; 41@; 12@] *
  cyc [:: 7@; 29@; 40@; 10@].

Definition Rmove : {perm facelet} :=
  cyc [:: 24@; 26@; 31@; 29@] * cyc [:: 25@; 28@; 30@; 27@] *
  cyc [:: 2@; 37@; 42@; 18@] * cyc [:: 4@; 35@; 44@; 20@] *
  cyc [:: 7@; 32@; 47@; 23@].

Definition Bmove : {perm facelet} :=
  cyc [:: 32@; 34@; 39@; 37@] * cyc [:: 33@; 36@; 38@; 35@] *
  cyc [:: 2@; 8@; 45@; 31@] * cyc [:: 1@; 11@; 46@; 28@] *
  cyc [:: 0@; 13@; 47@; 26@].

Definition Dmove : {perm facelet} :=
  cyc [:: 40@; 42@; 47@; 45@] * cyc [:: 41@; 44@; 46@; 43@] *
  cyc [:: 13@; 21@; 29@; 37@] * cyc [:: 14@; 22@; 30@; 38@] *
  cyc [:: 15@; 23@; 31@; 39@].

(* ---- 3. The move set S (18 HTM moves) and the cube group G --------------- *)

Definition faces : seq {perm facelet} :=
  [:: Umove; Rmove; Fmove; Dmove; Lmove; Bmove].

(* For each face: the quarter turn, the half turn, the inverse quarter turn.  *)
Definition moves : seq {perm facelet} :=
  flatten [seq [:: g; g ^+ 2; g ^-1] | g <- faces].

Definition Sset : {set {perm facelet}} := [set g in moves].

Definition G : {group {perm facelet}} := <<Sset>>.

(* A cube position is an element of G; the solved position is the identity.   *)
Definition position := {perm facelet}.
Definition solved : position := 1%g.

(* ---- 4. The subgroup H (Kociemba's / Thistlethwaite's G1) ---------------- *)
(*   A = {U1,U2,U3,D1,D2,D3,F2,B2,L2,R2}  (paper (4.1)),  H = <A>.            *)
(*   The A-generators are written to be *syntactically* among `moves`.        *)

Definition Amoves : seq {perm facelet} :=
  [:: Umove; Umove ^+ 2; Umove ^-1;
      Dmove; Dmove ^+ 2; Dmove ^-1;
      Fmove ^+ 2; Bmove ^+ 2; Lmove ^+ 2; Rmove ^+ 2].

Definition Aset : {set {perm facelet}} := [set g in Amoves].

Definition H : {group {perm facelet}} := <<Aset>>.

(* The partition of the cube group into the right cosets H*p.                 *)
Definition cosets := rcosets H G.

(* ---- 5. Structural facts ------------------------------------------------- *)

(* Every A-generator is one of the 18 moves.  A finite membership check, but   *)
(* proved structurally (no {perm 'I_48} is ever evaluated): each A-generator   *)
(* is syntactically one of the elements of `moves`.                           *)
Lemma A_sub_S : Aset \subset Sset.
Proof.
rewrite [Aset]set_cons !set_cons set_nil setU0 !setUA !subUset.
rewrite [Sset]set_cons !set_cons set_nil setU0.
by (repeat (apply/andP; split));
    repeat first [apply: subsetUl | apply: subsetU; apply/orP; right].
Qed.

(* H is a subgroup of G.  (Real proof, resting only on A_sub_S.)             *)
Lemma HsubG : H \subset G.
Proof. exact: genS A_sub_S. Qed.

(* [COMPUTATION] The order of the cube group (paper, p.1088). Stated for the  *)
(* record; the nat literal / evaluation is an external computation.           *)
(* Lemma card_G : #|G| = 43252003274489856000%N.  (* [COMPUTATION] *) *)
(* Lemma card_H : #|H| = 19508428800%N.            (* [COMPUTATION] *) *)
(* index #|G : H| = 2217093120 then follows from Lagrange (a real proof).     *)
