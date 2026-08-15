(* Canonical representatives, and the cover they give for nothing.           *)
(*                                                                           *)
(* Diameter.v assumes two things about the set R the external search is      *)
(* supposed to supply: that every coset is carried into R by a symmetry, and *)
(* that everything in R is solvable in twenty moves.  The first of those is  *)
(* not a computation.  Pick R to be the least member of each orbit and it    *)
(* holds because a finite set has a least element.                           *)
(*                                                                           *)
(* Nothing here enumerates anything.  The orbit of one coset under sixteen   *)
(* symmetries is the only finite object touched, and even that only through  *)
(* arg_minnP.  In particular no tactic ever computes on {set {perm facelet}} *)
(* which has 2^(48!) elements.                                               *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import Ball.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope group_scope.

Section Canon.

Variable gT : finGroupType.
Variable K : {group gT}.

(* What C becomes under each symmetry in K.                                  *)
Definition sorb (C : {set gT}) : {set {set gT}} := [set C :^ u | u in K].

Lemma sorb_id C : C \in sorb C.
Proof. by apply/imsetP; exists 1; rewrite ?group1 ?conjsg1. Qed.

(* The least member of that orbit, in the order the finite type already has. *)
(* Any choice that lands in the orbit would do; least is the shortest to     *)
(* write and it makes the choice canonical.                                  *)
Definition scanon (C : {set gT}) : {set gT} :=
  [arg min_(D < C | D \in sorb C) (enum_rank D : nat)].

Lemma scanon_mem C : scanon C \in sorb C.
Proof. by rewrite /scanon; case: arg_minnP => [|D]; [exact: sorb_id|]. Qed.

Lemma scanon_ex C : exists2 u, u \in K & C :^ u = scanon C.
Proof. by have /imsetP[u uK ->] := scanon_mem C; exists u. Qed.

Variable Cs : {set {set gT}}.

Definition Rcanon : {set {set gT}} := [set scanon C | C in Cs].

(* The cover, and it is a theorem rather than a hypothesis.                  *)
Lemma Rcanon_cover C : C \in Cs -> exists2 u, u \in K & C :^ u \in Rcanon.
Proof.
move=> CCs; have [u uK cu] := scanon_ex C.
by exists u => //; rewrite cu; apply/imsetP; exists C.
Qed.

(* And nothing outside the orbits gets in.                                   *)
Lemma Rcanon_sub : Rcanon \subset \bigcup_(C in Cs) sorb C.
Proof.
apply/subsetP => D /imsetP[C CCs ->].
by apply/bigcupP; exists C => //; exact: scanon_mem.
Qed.

End Canon.

(* The diameter bound with the cover discharged: one hypothesis is left, and *)
(* it is the one an exhaustive search has to supply.                         *)
Section CanonDiam.

Variable gT : finGroupType.
Variables (S : {set gT}) (H K : {group gT}).

Theorem diam_le_canon n :
  H \subset <<S>> -> S^-1 = S ->
  (forall u, u \in K -> S :^ u = S) ->
  (forall D, D \in Rcanon K (rcosets H <<S>>) -> D \subset ball S n) ->
  diam_le S n.
Proof.
move=> HS SV KS Hrad.
apply: (@diam_le_reps2 _ S H (Rcanon K (rcosets H <<S>>)) n) => // C CH.
have [u uK uR] := Rcanon_cover K CH.
by exists u; [exact: KS | rewrite uR].
Qed.

End CanonDiam.
