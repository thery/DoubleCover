(* A CHECK, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* The two corner sweeps of obligation C, run.  HEdgeChk does the edges.      *)
(*                                                                            *)
(*   rocq compile -R . Rubik HCornerChk.v                                     *)
(*                                                                            *)
(* IT MUST PRINT 70, true, 2187, true.                                        *)
(*                                                                            *)
(* THE cl DATUM is which of the eight places hold the four U corners, so an   *)
(* eight bit vector with four ones, and a turn PERMUTES it -- cplace_step     *)
(* says the new place j holds what the old place cplc m j held.  That is the  *)
(* whole rule, and it is why this is the easiest of the three.                *)
(*                                                                            *)
(* THE ct DATUM is the seven free twists.  A turn permutes them and adds the  *)
(* twist it brings in, and for j whose cplc is the eighth place the eighth    *)
(* twist is wanted -- SO IT IS RECOMPUTED, as minus the sum of the seven.     *)
(* That is the prototype's way, and what makes it right is that the eight     *)
(* twists of a real position sum to zero mod three.                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound HEdge
        HCorner HTables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the U corners among the eight places -------------------------------- *)

Definition cldat : seq (seq bool) :=
  [seq b <- [seq [seq ((j %/ 2 ^ i) %% 2)%N == 1%N | i <- iota 0 8]
            | j <- iota 0 256] | count id b == 4%N].

Eval vm_compute in seq.size cldat.

(* clcoordi with the position taken out of it                                *)
Definition clrk (b : seq bool) : int :=
  (foldl (fun ax j => let: (a, x) := ax in
       if nth false b j
       then (Uint63.add a (of_nat 'C(7 - j, x + 1)), (x + 1)%N)
       else (a, x))
     (0%uint63, 0%N) (rev (iota 0 8))).1.

(* a turn permutes the places                                                *)
Definition clstep (m : nat) (b : seq bool) : seq bool :=
  [seq nth false b (cplc m j) | j <- iota 0 8].

Definition chk_cl : bool :=
  all (fun b => all (fun m =>
        clrk (clstep m b)
          == PArray.get h_mt_cl
               (Uint63.add (Uint63.mul (clrk b) nqti) (of_nat m)))
      (iota 0 nq)) cldat.

Eval vm_compute in chk_cl.

(* ---- the seven free twists ----------------------------------------------- *)

Definition ctdat : seq (seq nat) :=
  [seq [seq ((j %/ 3 ^ i) %% 3)%N | i <- iota 0 7] | j <- iota 0 2187].

Eval vm_compute in seq.size ctdat.

(* the eighth, recomputed: the eight sum to zero mod three                    *)
Definition ct8 (t : seq nat) : nat := ((3 - (sumn t) %% 3) %% 3)%N.

Definition ctget (t : seq nat) (j : nat) : nat :=
  if (j < 7)%N then nth 0%N t j else ct8 t.

Definition ctrk (t : seq nat) : int :=
  foldl (fun a j => Uint63.add (Uint63.mul a (of_nat nslot))
                               (of_nat (nth 0%N t j)))
        0%uint63 (rev (iota 0 7)).

Definition ctstep (m : nat) (t : seq nat) : seq nat :=
  [seq ((ctget t (cplc m j) + (3 - ctw m j)) %% 3)%N | j <- iota 0 7].

Definition chk_ct : bool :=
  all (fun t => all (fun m =>
        ctrk (ctstep m t)
          == PArray.get h_mt_ct
               (Uint63.add (Uint63.mul (ctrk t) nqti) (of_nat m)))
      (iota 0 nq)) ctdat.

Eval vm_compute in chk_ct.
