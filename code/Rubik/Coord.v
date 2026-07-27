(* =========================================================================  *)
(*  Coord.v                                                                   *)
(*                                                                            *)
(*  The pruning heuristic Search.v asks for, built from a SUMMARY of a        *)
(*  position.                                                                 *)
(*                                                                            *)
(*  A summary is a map coord : position -> X into a small set, together with  *)
(*  an action of the moves on X such that                                     *)
(*                                                                            *)
(*      coord (g * m)  =  act (coord g) m                                     *)
(*                                                                            *)
(*  Forgetting information can only make solving easier, so the distance in   *)
(*  X is a lower bound on the distance in the group -- which is exactly what  *)
(*  a pruning heuristic must be.  Section Heuristic below turns any such      *)
(*  summary, together with ANY table D on X passing two local checks, into    *)
(*  the h that Search.v wants.  That part is proved.                          *)
(*                                                                            *)
(*  Everything specific to a particular summary is then a leaf, listed as an  *)
(*  explicit Parameter/Axiom so that Print Assumptions names it.  There are   *)
(*  five, and each is discharged in a known way:                              *)
(*                                                                            *)
(*    coordf, actf   definitions (3a)                                         *)
(*    coordfM        the equivariance -- the only real mathematics; for an    *)
(*                   orientation summary it is the cocycle identity           *)
(*                       t (g * m) f = t g (m f) + t m f                      *)
(*                   and for a position summary it is definitional      (3a)  *)
(*    Df             the table, built by breadth first search in the kernel;  *)
(*                   NEVER proved correct, only checked below           (3c)  *)
(*    Df0, DfStep    the two local checks, both finite computations, i.e.     *)
(*                   one vm_compute over X and over X * moves          (3d)   *)
(*                                                                            *)
(*  SIZE.  X is the summary, not the cube: the development uses the edge      *)
(*  orientations alone, 2048 summaries, where every computation is instant.   *)
(*  The real proof uses twist x flip x slice, 2 217 093 120 summaries.  Only  *)
(*  the numbers differ -- the statements and the proof scripts below are the  *)
(*  same either way.                                                          *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball Table Rubik333 Sym Search Root.

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
Parameter Xf : Type.
Parameter coordf : {perm facelet} -> Xf.
Parameter actf : Xf -> {perm facelet} -> Xf.

(* [3a] the equivariance: the only statement here that is not a computation.  *)
Axiom coordfM : forall g m, coordf (g * m) = actf (coordf g) m.

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
