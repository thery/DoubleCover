(* =========================================================================  *)
(*  HRunS.v -- obligation E: the search is sound when it fails.              *)
(* =========================================================================  *)

(* HSound.run_sound is the statement; this file is the proof of it.          *)
(*                                                                            *)
(* THE LOOP OVER THE MOVES IS AN ANONYMOUS fix INSIDE hsearch, and nothing    *)
(* can be said about it from outside.  Naming it in HSearch.v would change    *)
(* hsearch, and the seventy two run files prove statements about hsearch --   *)
(* 45.9 CPU-h to redo.  So the loop is copied here under a name, and hsearchE *)
(* says the copy is what hsearch runs.  That equation holds by conversion, so *)
(* it costs nothing and hsearch itself is untouched.                         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Ball Moves Coordfs Coordfsi
        Phase1 HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

Section RunS.

Variable mt_e mt_cl mt_ct : arr.
Variable which fam sym_cl sym_ct : arr.
Variable hfold : PArray.array arr.

Local Notation hsrch :=
  (hsearch mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold).
Local Notation stp := (stepa mt_e mt_cl mt_ct).
Local Notation hl := (hle which fam sym_cl sym_ct hfold).
Local Notation hal := (hale which fam sym_cl sym_ct hfold).
Local Notation hsol := hsolved.

(* ---- the move loop, named ------------------------------------------------ *)

(* THE PARAMETERS ARE SECTIONED, and that is what makes the equation hold by  *)
(* conversion: a Fixpoint taking them before the list is a fix on eight       *)
(* arguments, and no partial application of it is the anonymous fix, which    *)
(* recurses on the list alone.  Sectioned, hgo is a lambda over the seven     *)
(* with the fix inside, so applying it to seven arguments gives back exactly  *)
(* that fix.                                                                  *)
Section Go.

Variable d' : nat.
Variable di' : int.
Variable a0 : arr.
Variable path : seq int.
Variable x0 x1 x2 : hv.

Fixpoint hgo (l : seq (amv * nat)) : bool :=
  if l is mp :: l' then
    let: (m, pk) := mp in
    let: (k18, (k0, k1, k2)) := m in
    let y0 := stp x0 k0 in
    if hal y0 di' then
      let y1 := stp x1 k1 in
      if hal y1 di' then
        let y2 := stp x2 k2 in
        if hal y2 di' then
          if hsrch d' di' a0 (k18 :: path) (y0, y1, y2) pk
          then true else hgo l'
        else hgo l'
      else hgo l'
    else hgo l'
  else false.

End Go.

(* the copy is what hsearch runs, by conversion                              *)
Lemma hsearchE d di a0 path x0 x1 x2 p :
  hsrch d di a0 path (x0, x1, x2) p =
  if hl (x0, x1, x2) di then
    if (if hsol (x0, x1, x2) then eq_tabi flast (rebuild a0 path) idi
        else false)
    then true
    else if d is d'.+1 then
      hgo d' (Uint63.sub di 1%uint63) a0 path x0 x1 x2 (nth [::] hmoves p)
    else false
  else false.
Proof. by case: d. Qed.

(* ---- the loop finds what is in it ---------------------------------------- *)

(* All the completeness direction needs of the loop: if one entry passes its  *)
(* three guards and its search succeeds, the loop says true -- whatever the   *)
(* entries before it do.                                                      *)
Lemma hgo_true d' di' a0 path x0 x1 x2 l k18 k0 k1 k2 pk :
  ((k18, (k0, k1, k2)), pk) \in l ->
  hal (stp x0 k0) di' -> hal (stp x1 k1) di' -> hal (stp x2 k2) di' ->
  hsrch d' di' a0 (k18 :: path) (stp x0 k0, stp x1 k1, stp x2 k2) pk ->
  hgo d' di' a0 path x0 x1 x2 l.
Proof.
elim: l => [|[[j18 [[j0 j1] j2]] jpk] pl ih] //=.
rewrite inE => /orP[/eqP [] e18 e0 e1 e2 epk|hm] g0 g1 g2 hs.
  by rewrite -e0 -e1 -e2 -e18 -epk g0 g1 g2 hs.
case: ifP => h0; last by apply: ih.
case: ifP => h1; last by apply: ih.
case: ifP => h2; last by apply: ih.
by case: ifP => h3; last by apply: ih.
Qed.

(* ---- the loop is offered every turn the rule allows ---------------------- *)

(* hmoves is a table of lists, so this is a computation over the twenty five  *)
(* classes and twelve turns rather than a fact about the comprehension it was *)
(* built from.                                                                *)
Lemma hmoves_tab :
  all (fun p => all (fun m => allowedq p m ==>
        ((nth anull amoves m, hclass p m) \in nth [::] hmoves p))
      (iota 0 nq)) (iota 0 nclass).
Proof. by vm_compute. Qed.

Lemma hmoves_mem p m : (p < nclass)%N -> (m < nq)%N -> allowedq p m ->
  ((nth anull amoves m), hclass p m) \in nth [::] hmoves p.
Proof.
move=> pL mL ap.
by have /implyP := allP (allP hmoves_tab _ (mem_iota0 pL)) _ (mem_iota0 mL);
   apply.
Qed.

End RunS.

(* ---- what is left of run_sound ------------------------------------------- *)

(* The proof is the contrapositive: if an accepted word of at most d turns    *)
(* solves the position the search stands at, the search says true.  It is an  *)
(* induction on that word, and the pieces above are its skeleton -- hsearchE  *)
(* to see one step of the search, hmoves_mem to know the turn is offered,     *)
(* hgo_true to know the loop takes it.                                        *)
(*                                                                            *)
(* WHAT THE INDUCTION STILL NEEDS, and none of it is about the recursion:     *)
(*                                                                            *)
(*   the state IS the position.  x is the triple of rebuild a0 path along     *)
(*     each of the three axes, and stays so when a turn is played.  That is   *)
(*     obligation C, three times, once per axis -- the axes differ only by    *)
(*     the relabelling cmv, so the third instance is the same theorem.        *)
(*   a cut throws nothing away.  hle and hale must hold whenever a solution   *)
(*     of the remaining depth exists, which is HAdmis.h_cut once h is the     *)
(*     table read through the coordinates -- obligation D, whose sweep is     *)
(*     proved (HSweep, hsweep_all) and whose bridge to positions is C again.  *)
(*   the solved test is complete.  A solved position has triple h0, so        *)
(*     hsolved says true and the table rebuild agrees -- one lookup and C.    *)
(*   the depth in int63 is the depth in nat, for at most 24 of them.          *)
(*                                                                            *)
(* So E is now waiting on C, not on anything about the search.                *)
