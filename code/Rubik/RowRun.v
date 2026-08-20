(* =========================================================================  *)
(*  RowRun.v -- the search, the level loop, and what each owes.               *)
(* =========================================================================  *)

(* A level does two things.  The PREPASS plays the ten moves of H on the      *)
(* whole map at once, which accounts for every word ending in a move of H --  *)
(* and that is nearly all of them.  The SEARCH then looks for the words of    *)
(* that length whose last move is not in H.                                   *)
(*                                                                            *)
(* EVERY CUT HERE IS SAFE, and that is the whole reason a row is cheaper to   *)
(* prove than a lower bound.  What is proved is that the map FILLED, not that *)
(* the search was complete, so a cut that loses words can only make the row   *)
(* finish later or not at all -- it can never call a member covered when it   *)
(* is not.  So nothing below asks the search for completeness.  Compare       *)
(* HSound.canon and HRunS, which are that missing half for the quarter turns  *)
(* and which cost more than everything else together.                         *)
(*                                                                            *)
(* The search stops at a depth of its own and the prepass carries on alone,   *)
(* which is how twenty is reached: hcoset searches to about sixteen.          *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section Run.

(* ---- the layout, from Row.v ---------------------------------------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).
Local Notation mok := (membok par8 par4).

(* ---- the prepass, from RowMap.v ------------------------------------------ *)

Variable mpg mgr msw mlo mhi : arr.

Local Notation prep := (prepass mpg mgr msw mlo mhi).

(* ---- the phase one table, and the moves ---------------------------------- *)

(* The table hcoset's phase1prune carries: beside the distance to H, WHICH    *)
(* MOVES GO CLOSER.  A node then tries three or four moves instead of         *)
(* eighteen.  It is chunked like every other big table.                       *)
Variable p1 : PArray.array arr.

Definition p1get (c : int) : int :=
  PArray.get (PArray.get p1 (Uint63.lsr c cshft)) (Uint63.land c cmskw).

Definition wdist (w : int) : int := Uint63.land w 31%uint63.
Definition allmv : int := 262143%uint63.       (* the eighteen moves          *)

(* A move changes the distance by at most one, so a node with s moves to      *)
(* spare beyond its distance may take any move if s is two or more, one that  *)
(* does not raise if s is one, and only one that drops if s is nought.        *)
Definition wmask (w : int) (s : nat) : int :=
  if (2 <= s)%N then allmv
  else if s == 1%N then Uint63.land (Uint63.lsr w 23%uint63) allmv
  else Uint63.land (Uint63.lsr w 5%uint63) allmv.

(* the coordinate and the member, each stepped by a move                      *)
Variable cstep : int -> int -> int.
Variable xstep : memb -> int -> memb.

(* the redundancy rule, as the moves each face allows next                    *)
Variable okmv : int -> int -> bool.

Definition nmvn : nat := 18.

(* ---- the search ---------------------------------------------------------- *)

(* It is handed the moves worth trying, so it never builds a position the     *)
(* table has already ruled out.  At the bottom the coordinate is solved, so   *)
(* the member reached is one of the row and its bit goes in.                  *)
Fixpoint srch (togo : nat) (c : int) (x : memb) (msk : int) (pv : int)
              (m : rmap) : rmap :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then m'
         else if ~~ okmv pv k then m'
         else
           let c' := cstep c k in
           let w := p1get c' in
           let nd := Uint63.to_nat (wdist w) in
           if (nd <= togo')%N
           then srch togo' c' (xstep x k) (wmask w (togo' - nd)) k m'
           else m')
      m
  else let: (pg, gr, bt) := plc x in mmark m pg gr bt.

(* ---- one level, and the run ---------------------------------------------- *)

Variable croot : int.                  (* the row's coordinate               *)
Variable xroot : memb.                 (* and the member it starts from      *)
Variable dsrch : nat.                  (* where the search gives up          *)

Definition level (d : nat) (m : rmap) : rmap :=
  let m' := prep m in
  if (d <= dsrch)%N then
    let w := p1get croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then srch d croot xroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

Fixpoint run (n : nat) (d : nat) (m : rmap) : rmap :=
  if n is n1.+1 then run n1 d.+1 (level d m) else m.

(* ---- what the two halves owe --------------------------------------------- *)

(* The bridge to the cube: which position of the row a member stands for.     *)
Variable pos : memb -> {perm facelet}.

Definition wthn (d : nat) (x : memb) : Prop := pos x \in ball Sset d.

(* a map is sound at d when every bit it has set is a member within d         *)
Definition soundat (m : rmap) (d : nat) : Prop :=
  forall pg gr bt,
    inrange pg gr bt -> mtest m pg gr bt -> wthn d (unplc pg gr bt).

(* THE PREPASS OWES: a bit it sets is a member one move of H further than one *)
(* already set.  That is where the page, group and bit tables are spent, and  *)
(* it is one move -- not an induction over words.                             *)
Lemma prepass_sound m d : soundat m d -> soundat (prep m) d.+1.
Proof. Admitted.

(* THE SEARCH OWES: a bit it sets is a member of the row reached by the word  *)
(* it played.  An induction on the word, and nothing more: the search is      *)
(* never asked to have found everything.                                      *)
Lemma srch_sound togo c x msk pv m d :
  soundat m d -> wthn (d - togo) x -> soundat (srch togo c x msk pv m) d.
Proof. Admitted.

Lemma level_sound m d : soundat m d -> soundat (level d.+1 m) d.+1.
Proof. Admitted.

(* and so the whole run                                                       *)
Lemma run_sound n d m : soundat m d -> soundat (run n d m) (d + n).
Proof. Admitted.

End Run.
