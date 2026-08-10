(* =========================================================================  *)
(*  Coord.v -- The pruning heuristic Search.v asks for, built from a        *)
(*     SUMMARY of a position.                                               *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Ball Rubik333 Sym Search Root.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- 1. Any summary with any checked table gives a heuristic ------------- *)

Section Heuristic.

Variable X : Type.
Variable coord : {perm facelet} -> X.
Variable act : X -> {perm facelet} -> X.
Hypothesis coordM : forall g m, coord (g * m) = act (coord g) m.

(* The table.  Nothing is assumed about how it was produced.                  *)
Variable D : X -> nat.
Hypothesis D0 : D (coord 1) = 0.
Hypothesis Dstep : forall x m, m \in Sset -> D x <= (D (act x m)).+1.

Definition hcoord (g : {perm facelet}) : nat := D (coord g).

Lemma hcoord0 : hcoord 1 = 0.
Proof. by rewrite /hcoord D0. Qed.

Lemma hcoordS g m : m \in Sset -> hcoord g <= (hcoord (g * m)).+1.
Proof. by move=> mS; rewrite /hcoord coordM; apply: Dstep. Qed.

End Heuristic.

(* ---- 2. The summary itself: THE LEAVES ----------------------------------  *)

(* [3a] the summary and the action of a move on it.                           *)

(* ANY colouring of the facelets gives a summary, and hence an admissible     *)
(* heuristic; only the strength depends on the choice.  The real proof uses   *)
(* the colouring whose summary is the edge orientation.                       *)
Definition ecol (f : facelet) : bool := odd f.

Definition Xf : Type := {ffun facelet -> bool}.

(* The summary is read on g^-1, which is what makes it an ACTION rather than  *)
(* a twisted product: mathcomp has (g * m) f = m (g f), so the cocycle comes  *)
(* out on the other side.                                                     *)
Definition coordf (g : {perm facelet}) : Xf :=
  [ffun f => ecol f (+) ecol (g^-1 f)].

Definition actf (x : Xf) (m : {perm facelet}) : Xf :=
  [ffun f => x (m^-1 f) (+) ecol f (+) ecol (m^-1 f)].

(* [3a] the equivariance: the only statement here that is not a computation.  *)
Lemma coordfM g m : coordf (g * m) = actf (coordf g) m.
Proof.
apply/ffunP => f; rewrite /coordf /actf !ffunE invMg permM.
by case: (ecol f); case: (ecol (m^-1 f)); case: (ecol (g^-1 (m^-1 f))).
Qed.

(* [3c] the table, by breadth first search on Xf.  Never proved correct.      *)
Parameter Df : Xf -> nat.

(* [3d] the two local checks, both finite computations.                       *)
Axiom Df0 : Df (coordf 1) = 0.
Axiom DfStep : forall x m, m \in Sset -> Df x <= (Df (actf x m)).+1.

(* ---- 3. What that buys: the search, and a negative answer is a proof ----- *)

Definition hf : {perm facelet} -> nat := hcoord coordf Df.

Lemma hf0 : hf 1 = 0.
Proof. exact: (@hcoord0 Xf coordf Df Df0). Qed.

Lemma hfS g m : m \in Sset -> hf g <= (hf (g * m)).+1.
Proof. exact: (@hcoordS Xf coordf actf coordfM Df DfStep g m). Qed.

Definition searchf : nat -> {perm facelet} -> bool := search moves hf.

Corollary searchfN d g : searchf d g = false -> g \notin ball Sset d.
Proof. exact: (@searchN _ moves Sset_inv hf hf0 hfS d g). Qed.

(* ---- 4. How Diameter.v will use it --------------------------------------- *)

(* With ball_root2 of Root.v, one search of depth d.+2 on a symmetric         *)
(* position becomes the independent searches of depth d under each pair of    *)
(* first moves, the first of the two taken from Sroot -- two instead of       *)
(* eighteen.  Each of those is one generated file, one lemma, one             *)
(* vm_cast_no_check, checked in parallel.                                     *)
Corollary far_of_search (g : {perm facelet}) d :
  (forall u, u \in Symg -> g ^ u = g) ->
  g != 1 ->
  (forall m, m \in moves -> g * m != 1) ->
  (forall m1 m2, m1 \in Sroot -> m2 \in moves ->
     searchf d (g * m1 * m2) = false) ->
  g \notin ball Sset d.+2.
Proof.
move=> gJ g1 gm1 gmm; apply: (ball_root2 gJ) => // m1 m2 m1R m2M.
by apply: searchfN; apply: gmm.
Qed.
