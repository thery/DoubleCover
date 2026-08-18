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

(* ---- the search rebuilds the position ------------------------------------ *)

(* The maneuver is carried as the list of turns played, newest first, and the *)
(* position is only ever rebuilt from it when the cosets say it might be      *)
(* solved.  These two say the list is the position, and that the three codes  *)
(* a turn carries are the turn seen from the three axes.                      *)
Lemma get_mtia k : (k < 18)%N -> PArray.get mtia (of_nat k) = mvi k.
Proof.
by case: k => [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]]]]] // _;
   vm_compute.
Qed.

Lemma amoves_nth m : (m < nq)%N ->
  nth anull amoves m =
    (of_nat (qt18 m), (of_nat (cmv 0 m), of_nat (cmv 1 m), of_nat (cmv 2 m))).
Proof.
by case: m => [|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]] // _; vm_compute.
Qed.

(* a word played on a position                                               *)
Definition aw (a : arr) (v : seq nat) : arr :=
  foldl (fun x m => comp_tabi flast x (mvq m)) a v.

Lemma aw_cons a m v : aw a (m :: v) = aw (comp_tabi flast a (mvq m)) v.
Proof. by []. Qed.

Lemma rebuild_cons a0 path m : (m < nq)%N ->
  rebuild a0 (of_nat (qt18 m) :: path)
    = comp_tabi flast (rebuild a0 path) (mvq m).
Proof.
move=> mL; rewrite /rebuild /= -/(rebuild a0 path) get_mtia //.
by apply: qt18_lt.
Qed.

Lemma hleE x0 x1 x2 di :
  hl (x0, x1, x2) di = [&& hal x0 di, hal x1 di & hal x2 di].
Proof. by rewrite /hle; case: (hal x0 di); case: (hal x1 di). Qed.

(* the depth in int63 is the depth in nat, and NEVER leave the bound to //:   *)
(* nwB is 2 ^ 63 and in unary it does not come back                          *)
Lemma small_nwB k : (k <= 48)%N -> (k < nwB)%N.
Proof. by move=> kL; apply: leq_ltn_trans n47_small. Qed.

Lemma of_nat_sub1 n :
  (n <= 24)%N -> Uint63.sub (of_nat n.+1) 1%uint63 = of_nat n.
Proof.
move=> nL.
have h1 : (n.+1 <= 48)%N by apply: leq_trans (_ : 25 <= 48)%N.
have h0 : (n <= 48)%N by apply: ltnW.
apply: to_nat_inj.
by rewrite to_nat_sub ?of_natK ?to_nat_1 ?subn1 //; try by apply: small_nwB.
Qed.

(* ---- THE SEARCH IS SOUND WHEN IT FAILS ----------------------------------- *)

(* Everything the search needs of the table and the coordinates, named.  pok  *)
(* is the positions it meets, stt the triples it carries.  All four are       *)
(* obligation C, or C through D: that a turn moves the triples by the tables, *)
(* that the solved position is recognised, and that a cut throws no maneuver  *)
(* away.                                                                      *)
Section Complete.

Variable pok : arr -> bool.
Variable stt : arr -> hst.

Hypothesis pok_step : forall a m, pok a -> (m < nq)%N ->
  pok (comp_tabi flast a (mvq m)).
Hypothesis stt_step : forall a m, pok a -> (m < nq)%N ->
  stt (comp_tabi flast a (mvq m)) =
    (stp (stt a).1.1 (of_nat (cmv 0 m)), stp (stt a).1.2 (of_nat (cmv 1 m)),
     stp (stt a).2 (of_nat (cmv 2 m))).
Hypothesis stt_sol : forall a, pok a -> eq_tabi flast a idi -> hsol (stt a).
Hypothesis stt_cut : forall a v n, pok a -> qw v -> (seq.size v <= n)%N ->
  (n <= 24)%N -> eq_tabi flast (aw a v) idi -> hl (stt a) (of_nat n).

(* If a word the rule accepts, of at most d turns, solves the position the    *)
(* search stands at, the search says true.  The induction is on the word: the *)
(* cut cannot refuse it, the loop is offered its first turn, and the rest is  *)
(* the same statement one turn on.                                            *)
Lemma hsearch_complete v : forall d a0 path p,
  (d <= 24)%N -> pok (rebuild a0 path) -> qw v -> okw p v -> (p < nclass)%N ->
  (seq.size v <= d)%N -> eq_tabi flast (aw (rebuild a0 path) v) idi ->
  hsrch d (of_nat d) a0 path (stt (rebuild a0 path)) p.
Proof.
elim: v => [|m v ih] d a0 path p dL pk vq ov pL vs hsl.
  have hc := stt_cut pk (v := [::]) isT (leq0n d) dL hsl.
  have hs := stt_sol pk hsl.
  case E : (stt (rebuild a0 path)) hc hs => [[y0 y1] y2] hc hs.
  by rewrite hsearchE hc hs hsl.
case: d dL vs => [|d'] dL vs; first by [].
have mL : (m < nq)%N by move: vq => /andP[].
have vqv : qw v by move: vq => /andP[].
have ap : allowedq p m by move: ov => /= /andP[].
have opv : okw (hclass p m) v by move: ov => /= /andP[].
have d'L : (d' <= 24)%N by apply: ltnW.
have vsz : (seq.size v <= d')%N by move: vs.
have hc := stt_cut pk vq vs dL hsl.
have pk' : pok (comp_tabi flast (rebuild a0 path) (mvq m)) by apply: pok_step.
have hsl' :
    eq_tabi flast (aw (comp_tabi flast (rebuild a0 path) (mvq m)) v) idi.
  by rewrite -aw_cons.
have hcc := stt_cut pk' vqv vsz d'L hsl'.
have hst := stt_step pk mL.
have hr := rebuild_cons a0 path mL.
have [pcL _ _ _] := hclass_ok pL mL ap.
have pkr : pok (rebuild a0 (of_nat (qt18 m) :: path)) by rewrite hr.
have hslr : eq_tabi flast (aw (rebuild a0 (of_nat (qt18 m) :: path)) v) idi.
  by rewrite hr.
have hrec := ih d' a0 (of_nat (qt18 m) :: path) (hclass p m) d'L pkr vqv opv
  pcL vsz hslr.
move: hrec; rewrite hr hst => hrec.
move: hcc; rewrite hst hleE => /and3P[g0 g1 g2].
case E : (stt (rebuild a0 path)) hc g0 g1 g2 hrec
  => [[y0 y1] y2] hc g0 g1 g2 hrec.
rewrite hsearchE hc.
case: ifP => [_|_]; first by [].
rewrite (of_nat_sub1 d'L).
apply: (hgo_true (k18 := of_nat (qt18 m)) (k0 := of_nat (cmv 0 m))
                 (k1 := of_nat (cmv 1 m)) (k2 := of_nat (cmv 2 m))
                 (pk := hclass p m)) => //.
by rewrite -(amoves_nth mL); apply: hmoves_mem.
Qed.

(* the same read the way the run files are read                              *)
Lemma hsearch_sound d a0 path v p :
  (d <= 24)%N -> pok (rebuild a0 path) -> qw v -> okw p v -> (p < nclass)%N ->
  (seq.size v <= d)%N ->
  hsrch d (of_nat d) a0 path (stt (rebuild a0 path)) p = false ->
  ~~ eq_tabi flast (aw (rebuild a0 path) v) idi.
Proof.
move=> dL pk vq ov pL vs hf; apply/negP => hsl.
by rewrite (hsearch_complete dL pk vq ov pL vs hsl) in hf.
Qed.

End Complete.

End RunS.

(* ---- what is left of run_sound ------------------------------------------- *)

(* hsearch_sound is the search half of E, and it is done.  Turning it into    *)
(* HSound.run_sound is two things, neither about the recursion:               *)
(*                                                                            *)
(*   the four hypotheses of the section above, which are obligation C -- the  *)
(*     triples are the position's, three axes, and they step with the tables; *)
(*     the solved position is recognised; and a cut throws no maneuver away,  *)
(*     which is HAdmis.h_cut over the sweep HSweep.admis, now proved;         *)
(*   the root, which is HBridge's work: the position the run searches from is *)
(*     Reid's, and `the rebuilt table is the identity' is `the maneuver ends  *)
(*     at the position'.                                                      *)
