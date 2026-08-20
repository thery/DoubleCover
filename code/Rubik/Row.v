(* =========================================================================  *)
(*  Row.v -- one row of the upper bound: its members, and each as a bit.      *)
(* =========================================================================  *)

(* A row is the set of positions whose summary is solved after a fixed        *)
(* position p is played first: every w with p * w in H, where H is generated  *)
(* by U, D and the four half turns.  It has 8! * 8! * 4! / 2 members, and     *)
(* the whole cube splits into 2 217 093 120 rows.                             *)
(*                                                                            *)
(* The upper bound for a row is that every member is within twenty moves, and *)
(* it is proved by marking a bit for each member the search or the prepass    *)
(* reaches and finding no bit left clear.  This file says which bit a member  *)
(* is, and it is the only place where that correspondence is settled.         *)
(*                                                                            *)
(* THE LAYOUT IS hcoset's, because it is what makes the prepass fast.  A page *)
(* is one corner permutation.  Inside a page a GROUP of twenty four bits is a *)
(* PAIR of outer edge permutations -- the two that differ by exchanging the   *)
(* cubies 0 and 1 -- and the twenty four bits are the twenty four middle      *)
(* permutations, the twelve even ones low and the twelve odd ones high.       *)
(* Which member of the pair a bit means is settled by parity and so costs     *)
(* nothing, which is what makes the pair a group and the group a machine word.*)
(*                                                                            *)
(* Everything is a Variable: this file compiles with no table at all.  The    *)
(* four small tables are what ocaml/rubik_row.ml already builds.              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the shape of a row -------------------------------------------------- *)

Definition npagei  : int := 40320%uint63.   (* corner permutations           *)
Definition ngroupi : int := 20160%uint63.   (* pairs of outer edge perms     *)
Definition nbiti   : int := 24%uint63.      (* middle permutations           *)
Definition nhalfi  : int := 12%uint63.      (* of one parity                 *)

Definition rowsize : int := 19508428800%uint63.

(* SIZES ARE int63 AND NEVER nat: 19 508 428 800 in unary does not exist.    *)
Lemma rowsizeE : rowsize = Uint63.mul (Uint63.mul npagei ngroupi) nbiti.
Proof. by vm_compute. Qed.

Section Row.

(* ---- the four small tables ---------------------------------------------- *)

(* An outer edge permutation is numbered so that the pair {q, q with the two  *)
(* cubies 0 and 1 exchanged} is {2k, 2k+1}, and so that the low bit is the    *)
(* PARITY.  Two things follow and the prepass needs both: a move sends a pair *)
(* to a pair, because exchanging two cubies before a move is the same as      *)
(* exchanging them after it; and the parity says which member of a pair a bit *)
(* means, so the pair is one group and nothing is lost.                       *)
Variable e8num e8inv : arr.         (* rank <-> number, 40320 each           *)

(* A middle permutation gets a bit, the even ones taking 0..11 and the odd    *)
(* ones 12..23, an odd one sitting where the even one it comes from by F2 is. *)
(* That makes F2 the exchange of the two halves and nothing else.             *)
Variable e4bit e4of : arr.          (* rank <-> bit, 24 each                 *)

(* the parity of a permutation, by rank                                       *)
Variable par8 : arr.
Variable par4 : arr.

(* ---- a member, as a place ------------------------------------------------ *)

(* A member of a row is three permutations: the eight corners, the eight      *)
(* edges outside the middle layer, and the four inside it.  They are given    *)
(* here by their ranks.                                                       *)
Definition memb := (int * int * int)%type.

Definition mcp (x : memb) : int := let: (c, _, _) := x in c.
Definition mud (x : memb) : int := let: (_, u, _) := x in u.
Definition mmp (x : memb) : int := let: (_, _, m) := x in m.

(* The three have to agree on parity, which is why a row has 8! * 8! * 4! / 2 *)
(* members and not more.                                                      *)
Definition membok (x : memb) : bool :=
  (PArray.get par8 (mcp x) =?
     Uint63.lxor (PArray.get par8 (mud x)) (PArray.get par4 (mmp x)))%uint63.

(* where a member stands: its page, its group, and its bit                    *)
Definition place (x : memb) : int * int * int :=
  (mcp x,
   Uint63.lsr (PArray.get e8num (mud x)) 1,
   PArray.get e4bit (mmp x)).

(* and back.  The bit names the middle permutation and the group names a pair *)
(* of outer ones; which of the pair is meant is settled by parity, and the    *)
(* numbering carries the parity in its low bit.                               *)
Definition unplace (pg gr bt : int) : memb :=
  let mp := PArray.get e4of bt in
  let p := Uint63.lxor (PArray.get par8 pg) (PArray.get par4 mp) in
  (pg, PArray.get e8inv (Uint63.add (Uint63.lsl gr 1) p), mp).

(* ---- what has to be true of all this ------------------------------------- *)

(* These four are the whole content of the layout, and nothing else in the    *)
(* development may look inside place or unplace.                              *)

Definition inrange (pg gr bt : int) : bool :=
  [&& (pg <? npagei)%uint63, (gr <? ngroupi)%uint63 & (bt <? nbiti)%uint63].

(* a place is in range                                                        *)
Lemma place_range x :
  membok x -> let: (pg, gr, bt) := place x in inrange pg gr bt.
Proof. Admitted.

(* reading a place back gives the member that was put there                   *)
Lemma unplace_place x :
  membok x -> let: (pg, gr, bt) := place x in unplace pg gr bt = x.
Proof. Admitted.

(* and every place in range comes from a member                               *)
Lemma place_unplace pg gr bt :
  inrange pg gr bt ->
  membok (unplace pg gr bt) /\ place (unplace pg gr bt) = (pg, gr, bt).
Proof. Admitted.

(* so the map has exactly one bit for each member                             *)
Lemma place_inj x y : membok x -> membok y -> place x = place y -> x = y.
Proof. Admitted.

End Row.
