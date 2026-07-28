(* =========================================================================  *)
(*  Coordfsi.v                                                                *)
(*                                                                            *)
(*  The flip x slice summary on the two computable levels, and the two        *)
(*  agreement lemmas that join them to the one on permutations.               *)
(*                                                                            *)
(*  SKELETON.  Definitions and statements are meant to be final; the real     *)
(*  proofs are Admitted, each with a note on how it goes.                     *)
(*                                                                            *)
(*  THE THREE LEVELS.  Coordfs.v defines the summary on {perm facelet},       *)
(*  which is where it is proved equivariant and where Search.v wants it.      *)
(*  Nothing there computes.  Tsearch.v runs on seq nat and Tabi.v on          *)
(*  PArray, so the summary has to exist there too and the three have to       *)
(*  agree:                                                                    *)
(*                                                                            *)
(*      coordi a  =  coordt (ti2t a)          arrays vs lists   (Tabi shape)  *)
(*      coordfs (pt t)  =  coordt t           lists vs perms    (ptE shape)   *)
(*                                                                            *)
(*  Only the array one ever runs.  The list one exists to be the middle of    *)
(*  the sandwich, exactly as ti2t does in Tabi.v.                             *)
(*                                                                            *)
(*  READING ON THE INVERSE.  The summary reads g^-1, so on a table it wants   *)
(*  inv_tab.  That is not a detour: ti2t_inv and ptV are already proved, so   *)
(*  the inverse is free on both bridges, and one inv_tabi per node -- 48      *)
(*  writes -- is cheaper than the 24 searches an index-based reading would    *)
(*  cost.                                                                     *)
(*                                                                            *)
(*  THE GUARD COSTS 10%.  Dt and Dti carry cubt, so the guard is re-checked   *)
(*  at every node: 48 reads against the composition's ~900 writes.  The       *)
(*  alternative -- carrying the guard as an invariant through Tsearch.v and   *)
(*  Tabi.v -- would change both files to save that, and is not worth it.      *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord Coordfs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* the facelet count, as Table.v takes it: tables have size n.+1 with n = 47  *)
Definition nfacelet := 48.

(* ---- 0. The two side conditions of Tabi.v, at n = 47 --------------------- *)

(* Toy.v proves the same two.  When the real assembly file lands, one copy    *)
(* goes and both read it from here.                                           *)
Lemma n47_small : 47.+1 < nwB.
Proof. by apply: (@ltn_nwB 6). Qed.

Lemma n47_len : (of_nat 47.+1 <=? PArray.max_length)%uint63.
Proof. by vm_compute. Qed.

(* ---- 1. The colourings as bit masks -------------------------------------- *)

(* pcol and scol are membership in a twelve or eight element list, which is a *)
(* search at every one of the 24 readings a node does.  As a 48 bit mask each *)
(* is one instruction, and the mask is a Definition over the same list, so    *)
(* there is no second copy of the data to get wrong.                          *)

Definition pmask : int := packn nfacelet (fun f => f \in eprim).
Definition smask : int := packn nfacelet (fun f => f \in drop 8 eprim ++ drop 8 esec).

(* what the masks are for: one bit test replaces the membership              *)
Lemma bit_pmask f : f < nfacelet -> nbit pmask f = pcol (inord f).
Proof. Admitted.

Lemma bit_smask f : f < nfacelet -> nbit smask f = scol (inord f).
Proof. Admitted.

(* the nat level pairing, and its agreement with the one on facelets         *)
Definition epairn (f : nat) : nat :=
  nth f (esec ++ eprim) (index f (eprim ++ esec)).

Lemma epairnE f : f < nfacelet -> epair (inord f) = inord (epairn f).
Proof. Admitted.

(* ---- 2. The summary on lists --------------------------------------------- *)

(* u is the INVERSE table: u f is the facelet whose sticker now sits at f,    *)
(* which is what g^-1 f means on this side.                                   *)
Definition ecoordt (u : seq nat) : int :=
  packn ncoord
    (fun k => if k < nedge
              then ~~ nbit pmask (nth 0%N u (nth 0%N eprim k))
              else nbit smask (nth 0%N u (nth 0%N eprim (k - nedge)))).

Definition coordt (t : seq nat) : int := ecoordt (inv_tab 47 t).

(* the guard, on a table: g commutes with the pairing, facelet by facelet     *)
Definition cubt (t : seq nat) : bool :=
  all (fun f => epairn (nth 0%N t f) == nth 0%N t (epairn f)) (iota 0 nfacelet).

(* ---- 3. The summary on arrays -------------------------------------------- *)

Definition ecoordi (u : arr) : int :=
  packn ncoord
    (fun k => if k < nedge
              then ~~ bit pmask (PArray.get u (of_nat (nth 0%N eprim k)))
              else bit smask (PArray.get u (of_nat (nth 0%N eprim (k - nedge))))).

Definition coordi (a : arr) : int := ecoordi (inv_tabi 47 a).

Definition cubti (a : arr) : bool :=
  all (fun f => PArray.get a (of_nat (epairn f)) =?
                of_nat (epairn (to_nat (PArray.get a (of_nat f)))))%uint63
      (iota 0 nfacelet).

(* ---- 4. Arrays against lists --------------------------------------------- *)

(* Both go the way ti2t_comp does: the summary is a packn over 24 indices,    *)
(* so each reduces to one entry, and one entry is nth_ti2t.  The inverse is   *)
(* already bridged by ti2t_inv.                                               *)

Lemma ecoordiE u : tabi_ok 47 u -> ecoordi u = ecoordt (ti2t 47 u).
Proof. Admitted.

Lemma coordiE a : tabi_ok 47 a -> coordi a = coordt (ti2t 47 a).
Proof. Admitted.

Lemma cubtiE a : tabi_ok 47 a -> cubti a = cubt (ti2t 47 a).
Proof. Admitted.

(* ---- 5. Lists against permutations --------------------------------------- *)

(* Here the work is ptE and inord: pt t i = inord (nth 0 t i), and pt         *)
(* (inv_tab t) = (pt t)^-1 is ptV, so g^-1 (eprimf p) is inord of an entry of *)
(* the inverse table.  Then bit_pmask and bit_smask turn the two colourings   *)
(* into the two masks and the two sides are the same packn.                   *)

Lemma coordtE t : tab_ok 47 t -> coordfs (pt 47 t) = coordt t.
Proof. Admitted.

Lemma cubtE t : tab_ok 47 t -> cubP (pt 47 t) = cubt t.
Proof. Admitted.

(* ---- 6. The heuristic at each level, in the shape the searches want ------ *)

Section Heuristic.

(* [3c] the table.  Item 3 replaces this by a Definition reading a packed     *)
(* PArray, and Dfs0/DfsStep by two checked computations.                      *)
Variable Dfs : int -> nat.
Hypothesis Dfs0 : Dfs (coordfs 1) = 0.
Hypothesis DfsStep : forall x m, m \in Sset -> Dfs x <= (Dfs (actfs x m)).+1.

(* the guard is re-read at each level rather than carried as an invariant     *)
Definition Dt (t : seq nat) : nat := if cubt t then Dfs (coordt t) else 0.
Definition Dti (a : arr) : nat := if cubti a then Dfs (coordi a) else 0.

(* THE TWO BRIDGES, in exactly the shape searchtE and searchiE ask for.       *)
Lemma hfsE t : tab_ok 47 t -> hfs Dfs (pt 47 t) = Dt t.
Proof. Admitted.

Lemma DtiE a : tabi_ok 47 a -> Dti a = Dt (ti2t 47 a).
Proof. Admitted.

(* ---- 7. And hence the whole chain ---------------------------------------- *)

(* The moves as arrays, and the one fact tying them to Rubik333.moves; the    *)
(* assembly file supplies both, exactly as Toy.v does today.                  *)
Variable mtis : seq arr.
Hypothesis mtis_ok : all (tabi_ok 47) mtis.
Hypothesis mtisE :
  moves = [seq pt 47 mt | mt <- [seq ti2t 47 mt | mt <- mtis]].

(* what the depth 12 theorem will cite: one false answer from the array       *)
(* search, and the position is out of the ball.                              *)
Corollary far_of_searchi d a :
  tabi_ok 47 a -> searchi 47 mtis Dti d a = false ->
  pt 47 (ti2t 47 a) \notin ball Sset d.
Proof.
move=> aok sE; apply: (searchfsN Dfs0 DfsStep (d := d)).
rewrite /searchfs mtisE.
by apply: (searchiN n47_small n47_len mtis_ok DtiE hfsE aok sE).
Qed.

End Heuristic.
