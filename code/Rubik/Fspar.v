(* =========================================================================  *)
(*  Fspar.v -- checkStep, split sixteen ways so it can be run on several    *)
(*     cores.                                                               *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Coordfs Fstab FsTable Moves.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the shape of the split ---------------------------------------------- *)

Definition cbits := 20.                 (* width of one slice, in bits        *)
Definition nchunk := 16.                (* 2 ^ (ncoord - cbits)               *)

(* the start of slice n.  cstart n is a closed int, so every equation between
   it and the offsets the split produces is one vm_compute on integers --
   the predicate is never in scope of that computation.                  *)
Definition cstart (n : nat) : int := (of_nat n * lsl 1 (of_nat cbits))%uint63.

(* the predicate checkStep runs, at the real table and the real moves.
   Fstab.v names it so that this is a delta step: an equation between two
   closed all_pow ncoord terms would make conversion commute the let past
   all_pow, which unfolds the loop into 2 ^ 24 conjuncts and never returns. *)
Definition chunkF : int -> bool := stepF fstab mtabs.

Lemma chunkFE : checkStep fstab mtabs = all_pow ncoord 0%uint63 chunkF.
Proof. by rewrite /checkStep /chunkF. Qed.

(* ---- the split ------------------------------------------------------------*)

(* one binary split, with k abstract so conversion can only take a single
   delta step -- with k concrete it would unfold the whole loop.          *)
Lemma all_powS k i (f : int -> bool) :
  all_pow k.+1 i f = all_pow k i f && all_pow k (i + lsl 1 (of_nat k))%uint63 f.
Proof. by []. Qed.

(* the sixteen offsets the four splits leave behind, each identified with the
   cstart it is.  Integer arithmetic only, so vm_compute is safe here.    *)
Lemma cs00 : cstart 0 = 0%uint63.
Proof. by vm_compute. Qed.
Lemma cs01 : (0 + lsl 1 (of_nat 20))%uint63 = cstart 1.
Proof. by vm_compute. Qed.
Lemma cs02 : (0 + lsl 1 (of_nat 21))%uint63 = cstart 2.
Proof. by vm_compute. Qed.
Lemma cs03 : (0 + lsl 1 (of_nat 21) + lsl 1 (of_nat 20))%uint63 = cstart 3.
Proof. by vm_compute. Qed.
Lemma cs04 : (0 + lsl 1 (of_nat 22))%uint63 = cstart 4.
Proof. by vm_compute. Qed.
Lemma cs05 : (0 + lsl 1 (of_nat 22) + lsl 1 (of_nat 20))%uint63 = cstart 5.
Proof. by vm_compute. Qed.
Lemma cs06 : (0 + lsl 1 (of_nat 22) + lsl 1 (of_nat 21))%uint63 = cstart 6.
Proof. by vm_compute. Qed.
Lemma cs07 : (0 + lsl 1 (of_nat 22) + lsl 1 (of_nat 21) + lsl 1 (of_nat 20))%uint63
             = cstart 7.
Proof. by vm_compute. Qed.
Lemma cs08 : (0 + lsl 1 (of_nat 23))%uint63 = cstart 8.
Proof. by vm_compute. Qed.
Lemma cs09 : (0 + lsl 1 (of_nat 23) + lsl 1 (of_nat 20))%uint63 = cstart 9.
Proof. by vm_compute. Qed.
Lemma cs10 : (0 + lsl 1 (of_nat 23) + lsl 1 (of_nat 21))%uint63 = cstart 10.
Proof. by vm_compute. Qed.
Lemma cs11 : (0 + lsl 1 (of_nat 23) + lsl 1 (of_nat 21) + lsl 1 (of_nat 20))%uint63
             = cstart 11.
Proof. by vm_compute. Qed.
Lemma cs12 : (0 + lsl 1 (of_nat 23) + lsl 1 (of_nat 22))%uint63 = cstart 12.
Proof. by vm_compute. Qed.
Lemma cs13 : (0 + lsl 1 (of_nat 23) + lsl 1 (of_nat 22) + lsl 1 (of_nat 20))%uint63
             = cstart 13.
Proof. by vm_compute. Qed.
Lemma cs14 : (0 + lsl 1 (of_nat 23) + lsl 1 (of_nat 22) + lsl 1 (of_nat 21))%uint63
             = cstart 14.
Proof. by vm_compute. Qed.
Lemma cs15 : (0 + lsl 1 (of_nat 23) + lsl 1 (of_nat 22) + lsl 1 (of_nat 21)
              + lsl 1 (of_nat 20))%uint63 = cstart 15.
Proof. by vm_compute. Qed.

(* f STAYS ABSTRACT THROUGHOUT.  A /= or a vm_compute here would unfold the
   loop into 2 ^ 24 conjuncts; this is the all_iota18 lesson from
   the glue of a split proof, where it looks like a hang.               *)
Lemma all_pow_glue16 (f : int -> bool) :
  all_pow cbits (cstart 0) f -> all_pow cbits (cstart 1) f ->
  all_pow cbits (cstart 2) f -> all_pow cbits (cstart 3) f ->
  all_pow cbits (cstart 4) f -> all_pow cbits (cstart 5) f ->
  all_pow cbits (cstart 6) f -> all_pow cbits (cstart 7) f ->
  all_pow cbits (cstart 8) f -> all_pow cbits (cstart 9) f ->
  all_pow cbits (cstart 10) f -> all_pow cbits (cstart 11) f ->
  all_pow cbits (cstart 12) f -> all_pow cbits (cstart 13) f ->
  all_pow cbits (cstart 14) f -> all_pow cbits (cstart 15) f ->
  all_pow ncoord 0%uint63 f.
Proof.
move=> h00 h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14 h15.
rewrite cs00 in h00.
rewrite /ncoord (all_powS 23) !(all_powS 22) !(all_powS 21) !(all_powS 20).
rewrite cs01 cs02 cs03 cs04 cs05 cs06 cs07 cs08 cs09 cs10 cs11 cs12 cs13 cs14 cs15.
by rewrite h00 h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14 h15.
Qed.
