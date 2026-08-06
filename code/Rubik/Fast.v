(* =========================================================================  *)
(*  Fast.v                                                                    *)
(*                                                                            *)
(*  searchz3 with every nat taken out of the inner loop.  NO PROOFS: this is  *)
(*  for measuring only.  searchz3f is not tied to searchz3 by anything yet.   *)
(*                                                                            *)
(*  What it removes, all MEASURED at 100 000 iterations, vm:                  *)
(*                                                                            *)
(*    allowedr p      60.4 us -> 2.55  precomputed, the answer depends only   *)
(*                                    on p, which takes 7 values              *)
(*    nth _ mtis k     8.67 us -> 0.17  an array, not a walk down 18 conses,  *)
(*                                    and it runs once a CHILD                *)
(*    of_nat d         1.57 us -> 0.10  the depth carried as an int as well   *)
(*    step3's two nth over mv3a/mv3b and three of_nat: precomputed with the   *)
(*    move index, so step3i does six array reads and nothing else.            *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Fsparity
        Farp1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the move tables as an array, indexed by an int --------------------- *)
Fixpoint setl (a : PArray.array arr) (i : int) (l : seq arr)
  : PArray.array arr :=
  if l is x :: l' then setl (PArray.set a i x) (Uint63.add i 1) l' else a.

Definition mtisa : PArray.array arr := Eval vm_compute in
  setl (PArray.make 18%uint63 (id_tabi 47)) 0%uint63 mtis.

(* ---- the seven allowed lists, with every index already an int ------------ *)
(* each entry is (k, mv3a k, mv3b k) as ints, and the child's p as a nat --
   p indexes a seven element list, so it is left alone *)
Definition amove := ((int * int) * int)%type.

Definition allowed3 : seq (seq (amove * nat)) := Eval vm_compute in
  [seq [seq (((of_nat k, of_nat (nth 0%N mv3a k)), of_nat (nth 0%N mv3b k)),
             fcpos k)
       | k <- allowedr mtis nfcube oppf fcpos p]
  | p <- iota 0 7].

(* ---- step3 with the indices already int63 -------------------------------- *)
Definition step3i (x : c3) (m : amove) : c3 :=
  let: (x0, x1, x2) := x in
  let: ((k, ka), kb) := m in
  ((acttwii x0.1 k, actfsri x0.2 k),
   (acttwii x1.1 ka, actfsri x1.2 ka),
   (acttwii x2.1 kb, actfsri x2.2 kb)).

(* ---- and the search.  d stays a nat for the recursion to be structural;
   di is the same number as an int, so h3i's test costs nothing. ------------ *)
Fixpoint searchz3f (T : PArray.array arr) (d : nat) (di : int) (a : arr)
                   (x : c3) (p : nat) : bool :=
  if (h3i T x <=? di)%uint63 then
    if eq_tabi 47 a (id_tabi 47) then true
    else if d is d'.+1 then
      let di' := Uint63.sub di 1%uint63 in
      (fix go (l : seq (amove * nat)) : bool :=
         if l is mp :: l' then
           let: (m, pk) := mp in
           if searchz3f T d' di' (comp_tabi 47 a (PArray.get mtisa m.1.1))
                          (step3i x m) pk
           then true else go l'
         else false) (nth [::] allowed3 p)
    else false
  else false.
