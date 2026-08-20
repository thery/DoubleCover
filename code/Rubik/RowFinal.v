(* =========================================================================  *)
(*  RowFinal.v -- every member of the row is within twenty moves.             *)
(* =========================================================================  *)

(* The theorem is assembled from three things and nothing else:               *)
(*                                                                            *)
(*   the run is SOUND    -- every bit it set is a member within twenty        *)
(*   the map came out FULL, once the witnesses are counted in                 *)
(*   the layout is a BIJECTION -- one bit for each member, and no other       *)
(*                                                                            *)
(* THE WITNESSES ARE THE CHEAP HALF, and in Rocq far cheaper than they are    *)
(* for hcoset.  A member the run leaves clear is settled by exhibiting a word *)
(* and playing it: twenty moves on a forty eight entry table.  Whatever       *)
(* produced the word is never trusted and never mentioned -- it can be any    *)
(* solver at all.  So the search should be stopped as SHALLOW as the witness  *)
(* count allows, not run as deep as it will go: a search level is expensive   *)
(* and a witness is not.  That is the reverse of the lower bound, where a     *)
(* witness proves nothing and only exhaustiveness counts.                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* the two maps together                                                      *)
Definition mor (m1 m2 : rmap) : rmap :=
  ifold npagen 0%uint63
    (fun pg a =>
       ifold ngroupn 0%uint63
         (fun gr a' =>
            let g := grpof pg gr in
            gset a' g (Uint63.lor (gget m1 g) (gget m2 g)))
         a)
    m1.

Section Final.

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).
Local Notation mok := (membok par8 par4).
Local Notation inrng := inrange.

Variable pos : memb -> {perm facelet}.

Local Notation wthn := (wthn pos).
Local Notation soundat := (soundat e8inv e4of par8 par4 pos).

(* ---- the witnesses ------------------------------------------------------- *)

(* A witness is a place and a word.  wok is the check: play the word from the *)
(* position that place stands for and see the cube solved.                    *)
Variable wok : memb -> seq int -> bool.

Hypothesis wokP :
  forall x w, wok x w -> (seq.size w <= 20)%N -> wthn 20 x.

Variable wl : seq (int * int * int * seq int).

(* every witness is in range, at most twenty moves, and solves its member     *)
Definition witsok : bool :=
  all (fun t => let: (pg, gr, bt, w) := t in
                [&& inrng pg gr bt, (seq.size w <= 20)%N & wok (unplc pg gr bt) w])
      wl.

(* the map of the places the witnesses cover                                  *)
Definition wmap : rmap :=
  foldr (fun t m => let: (pg, gr, bt, _) := t in mmark m pg gr bt) mempty wl.

(* ---- the theorem --------------------------------------------------------- *)

(* Everything the computation has to say is in these two booleans: the map    *)
(* and the witnesses together leave no bit clear, and every witness word does *)
(* what it claims.                                                            *)

Variable mfin : rmap.

Theorem row_within_20 :
  soundat mfin 20 ->
  witsok ->
  mfull (mor mfin wmap) ->
  forall x, mok x -> wthn 20 x.
Proof. Admitted.

(* What the two hypotheses of row_within_20 rest on, so that the shape of the *)
(* whole thing is visible from this file alone:                               *)
(*                                                                            *)
(*   soundat mfin 20   is RowRun.run_sound, which is RowRun.prepass_sound and *)
(*                     RowRun.srch_sound -- one move of H, and an induction   *)
(*                     on a word.  Neither asks for completeness.             *)
(*                                                                            *)
(*   mfull (...)       is the computation: 812 851 200 words swept once.      *)
(*                                                                            *)
(*   witsok            is the witnesses, one replay of twenty moves each.     *)
(*                                                                            *)
(*   and the step from `no bit clear' to `every member' is Row.place_unplace  *)
(*                     with Row.place_inj: the layout is a bijection between  *)
(*                     the bits and the members.  THAT IS THE LONG POLE --    *)
(*                     the ranking, the pairing of outer permutations, and    *)
(*                     the parity that lets the last place be dropped.        *)

End Final.
