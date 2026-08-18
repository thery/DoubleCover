(* A CHECK, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* WHAT IT CHECKS.  Obligation C for the edges says a turn moves the DATUM -- *)
(* where the four slice cubies sit and how they lie -- by a rule that does    *)
(* not look at the position, and that the move table is the ranking of that   *)
(* rule.  HEdge.v is proving the first half.  This runs the second, at every  *)
(* one of the 190080 data and every turn, which is the whole of the sweep C   *)
(* asks for.  It needs the small move tables only, not the folded one.        *)
(*                                                                            *)
(*   make mtabs                 (if HTables.v is not there)                   *)
(*   /usr/bin/time -v coqc -R . Rubik HEdgeChk.v                              *)
(*                                                                            *)
(* IT MUST PRINT true THREE TIMES.  The first two are cheap and are the ones  *)
(* that catch a wrong rule fastest: the ranking here is the ranking of        *)
(* HCoord, on Reid's six positions, and the step rule agrees with the table   *)
(* on those six.  The third is the sweep.                                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound HEdge
        HTables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the datum, and its rank -------------------------------------------- *)

(* The datum is the four values eslot reads, one per slice cubie: twice the   *)
(* place plus the flip.  erk is ecoordi with the position taken out of it.    *)
Definition edat (u : arr) : seq nat := [seq eslot u i | i <- iota 0 nslicec].

Definition erk (s : seq nat) : int :=
  (foldl (fun ru i => let: (r, used) := ru in
       let x := nth 0%N s i in
       let p := (x %/ 2)%N in
       let idx := (2 * count (fun q => q \notin used) (iota 0 p))%N in
       (Uint63.add (Uint63.add (Uint63.mul r (of_nat (2 * nedge - 2 * i)%N))
                               (of_nat idx))
                   (of_nat (x %% 2)%N), p :: used))
     (0%uint63, [::]) (iota 0 nslicec)).1.

(* CHECK 1: the rank of the datum is the coordinate, on Reid's six.          *)
Definition chk_rank : bool :=
  all (fun k => erk (edat (inv_tabi flast (rooti k)))
                  == (htriple (rooti k)).1.1) (iota 0 npfx).

Eval vm_compute in chk_rank.

(* ---- the rule ----------------------------------------------------------- *)

(* Where the place j' comes from: the turn takes it to eplc m j'.  So the     *)
(* cubie that was at place j is at the j' with eplc m j' = j, and it is       *)
(* turned over on the way exactly when eflp m j' is one.                      *)
Definition eplcinv (m j : nat) : nat :=
  index j [seq eplc m k | k <- iota 0 nedge].

Definition estep (m : nat) (s : seq nat) : seq nat :=
  [seq (let j := (x %/ 2)%N in let fl := (x %% 2)%N in
        let j' := eplcinv m j in (2 * j' + (fl + eflp m j') %% 2)%N) | x <- s].

(* CHECK 2: on Reid's six, the rule agrees with the move table.              *)
Definition chk_root : bool :=
  all (fun k =>
    all (fun m =>
      erk (estep m (edat (inv_tabi flast (rooti k))))
        == PArray.get h_mt_e
             (Uint63.add (Uint63.mul (erk (edat (inv_tabi flast (rooti k))))
                                     nqti) (of_nat m)))
      (iota 0 nq)) (iota 0 npfx).

Eval vm_compute in chk_root.

(* ---- the sweep ---------------------------------------------------------- *)

(* Every datum: four distinct places out of twelve, in order, and a flip on   *)
(* each.  12 * 11 * 10 * 9 * 16 = 190080, which is n_e exactly.               *)
Definition edata : seq (seq nat) :=
  flatten [seq
    flatten [seq
      flatten [seq
        [seq [:: a; b; c; d] | d <- iota 0 24 &
              [&& (d %/ 2)%N != (a %/ 2)%N, (d %/ 2)%N != (b %/ 2)%N
                & (d %/ 2)%N != (c %/ 2)%N]]
      | c <- iota 0 24 &
          ((c %/ 2)%N != (a %/ 2)%N) && ((c %/ 2)%N != (b %/ 2)%N)]
    | b <- iota 0 24 & (b %/ 2)%N != (a %/ 2)%N]
  | a <- iota 0 24].

Eval vm_compute in seq.size edata.

(* CHECK 3: the table is the ranking of the rule, at every datum and turn.   *)
Definition chk_from (l : seq (seq nat)) : bool :=
  all (fun s => all (fun m =>
        erk (estep m s)
          == PArray.get h_mt_e
               (Uint63.add (Uint63.mul (erk s) nqti) (of_nat m)))
      (iota 0 nq)) l.

(* ON A SLICE, and that is not caution -- erk and estep count in nat, and a  *)
(* nat operation is about a microsecond against 0.05 for an int63.  Two      *)
(* thousand data answer the question the sweep is asked, which is whether    *)
(* the rule is the table, and they give the cost of one datum so the whole   *)
(* 190080 can be scaled rather than guessed.  The whole sweep is the same    *)
(* line with edata for esmall, and it wants the datum in int63 first.        *)
Definition esmall : seq (seq nat) := take 2000 edata.

Time Eval vm_compute in chk_from esmall.
