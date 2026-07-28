(* =========================================================================  *)
(*  Coordfs.v                                                                 *)
(*                                                                            *)
(*  The flip x slice summary, packed into 24 bits of an int63.                *)
(*                                                                            *)
(*  SKELETON.  The definitions and the statements are meant to be final; the  *)
(*  proofs are all Admitted, each with a note on how it goes.                 *)
(*                                                                            *)
(*  WHY 24 BITS.  Coord.v turns any summary satisfying                        *)
(*                                                                            *)
(*      coord (g * m) = act (coord g) m                                       *)
(*                                                                            *)
(*  into an admissible heuristic, whatever table is put on it -- the table is *)
(*  never proved correct, it only has to pass Df0 and DfStep.  DfStep is a    *)
(*  statement about every element of the summary type, so that type has to be *)
(*  ENUMERABLE BY A LOOP: a finfun will not do, an int below 2 ^ 24 will.     *)
(*  Hence the packing, and hence the bit level reasoning below, which is the  *)
(*  only real work in this file.                                              *)
(*                                                                            *)
(*  WHY A GUARD.  The summary is about CUBIES: bit p of the flip half says    *)
(*  whether the sticker now at the primary facelet of edge position p is a    *)
(*  primary sticker.  For that to have an action one needs the two facelets   *)
(*  of an edge to stay together, which holds for a cube move but not for an   *)
(*  arbitrary permutation of 'I_48.  So coordM is guarded by cubP -- g        *)
(*  commutes with the involution pairing the two facelets of each edge.       *)
(*  Section Heuristic below shows the guard costs nothing downstream: h is    *)
(*  defined to be 0 off the guarded set, and then Search.v's two conditions   *)
(*  hold unconditionally, so Search.v does not change.                        *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Rubik333 Sym Search Root Coord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* uint63_scope is deliberately NOT opened: this file is mostly about perms
   and nat, and the scope would turn every 1 into an int.  The three int
   expressions below carry their own %uint63.                                *)

(* ---- 1. A summary that is only an action on part of the group ------------ *)

(* Coord.v's Section Heuristic asks for the equivariance at every g.  This is *)
(* the same construction with the equivariance only on a subgroup P, which is *)
(* all a cubie summary can offer.  h is 0 off P, and since P is closed under  *)
(* the moves the two conditions Search.v wants come out unconditional.        *)

Section HeuristicG.

Variable X : Type.
Variable P : pred {perm facelet}.
Hypothesis P1 : P 1.
Hypothesis PM : forall g m, P g -> m \in Sset -> P (g * m).

Variable coord : {perm facelet} -> X.
Variable act : X -> {perm facelet} -> X.
Hypothesis coordM :
  forall g m, P g -> m \in Sset -> coord (g * m) = act (coord g) m.

Variable D : X -> nat.
Hypothesis D0 : D (coord 1) = 0.
Hypothesis Dstep : forall x m, m \in Sset -> D x <= (D (act x m)).+1.

Definition hcoordg (g : {perm facelet}) : nat := if P g then D (coord g) else 0.

Lemma hcoordg0 : hcoordg 1 = 0.
Proof. by rewrite /hcoordg P1 D0. Qed.

(* The one place the guard is paid: off P there is nothing to prove because   *)
(* 0 is below everything, and on P the guard propagates by PM.                *)
Lemma hcoordgS g m : m \in Sset -> hcoordg g <= (hcoordg (g * m)).+1.
Proof.
move=> mS; rewrite /hcoordg; case: ifP => [Pg|_]; last by [].
by rewrite (PM Pg mS) coordM //; apply: Dstep.
Qed.

End HeuristicG.

(* ---- 2. The twelve edges ------------------------------------------------- *)

(* Read off the cycles of Rubik333.v.  A face holds its eight facelets as     *)
(*                                                                            *)
(*      0 1 2                                                                 *)
(*      3   4          U with B at the top, D with F at the top,              *)
(*      5 6 7          the side faces with U at the top,                      *)
(*                                                                            *)
(* so the edge facelets of a face are its offsets 1, 3, 4 and 6, and U is     *)
(* 0..7, L is 8..15, F is 16..23, R is 24..31, B is 32..39, D is 40..47.      *)
(* The pairing is forced by the cycles: Umove sends 3 to 1 and 9 to 33, so    *)
(* the edge (3, 9) goes to the edge (1, 33), and so on round the cube.        *)

(* The order is the classical one, UR UF UL UB DR DF DL DB FR FL BL BR.       *)
(* eprim is the U or D facelet of a U/D edge and the F or B facelet of a      *)
(* slice edge: exactly the convention under which F and B quarter turns flip  *)
(* the four edges they move and the other four faces flip nothing.            *)
Definition eprim : seq nat :=
  [:: 4; 6; 3; 1; 44; 41; 43; 46; 20; 19; 36; 35]%N.
Definition esec : seq nat :=
  [:: 25; 17; 9; 33; 30; 22; 14; 38; 27; 12; 11; 28]%N.

(* the twelve positions, and the four of them in the middle slice            *)
Definition nedge := 12.
Definition nslice := 4.

Definition eprimf (p : nat) : facelet := inord (nth 0%N eprim p).

(* the two colourings the summary reads.  pcol is one facelet of each edge,  *)
(* scol is both facelets of each slice edge -- that is what makes the slice  *)
(* half a plain permutation of bits with no correction term.                 *)
Definition pcol (f : facelet) : bool := (f : nat) \in eprim.
Definition scol (f : facelet) : bool :=
  (f : nat) \in drop 8 eprim ++ drop 8 esec.

(* the partner facelet, and the position an edge facelet belongs to          *)
Definition epair (f : facelet) : facelet :=
  nth f [seq (inord i : facelet) | i <- esec ++ eprim]
        (index (f : nat) (eprim ++ esec)).

Definition epos (f : facelet) : nat := index (f : nat) (eprim ++ esec) %% nedge.

(* ---- 3. What the data has to satisfy ------------------------------------- *)

(* All four are decided by vm_compute on the two lists, once inord is out of  *)
(* the way -- the values are literals, so each is a 24 element check.         *)

Lemma epairK : involutive epair.
Proof. Admitted.

Lemma pcol_epair (f : facelet) : (f : nat) \in eprim ++ esec -> pcol (epair f) = ~~ pcol f.
Proof. Admitted.

Lemma scol_epair f : scol (epair f) = scol f.
Proof. Admitted.

Lemma epos_prim p : p < nedge -> epos (eprimf p) = p.
Proof. Admitted.

(* an edge facelet is the primary or the secondary facelet of its position    *)
Lemma edge_case (f : facelet) : (f : nat) \in eprim ++ esec ->
  f = eprimf (epos f) \/ f = epair (eprimf (epos f)).
Proof. Admitted.

(* ---- 4. The guard: permutations that keep the two facelets of an edge      *)
(*         together --------------------------------------------------------- *)

Definition cubP (g : {perm facelet}) : bool :=
  [forall f : facelet, epair (g f) == g (epair f)].

(* It is the centraliser of an involution, so a subgroup; nothing here is     *)
(* about the cube.                                                            *)
Lemma cubP1 : cubP 1.
Proof. Admitted.

Lemma cubPM g h : cubP g -> cubP h -> cubP (g * h).
Proof. Admitted.

Lemma cubPV g : cubP g -> cubP (g^-1).
Proof. Admitted.

(* the moves keep cubies together.  Eighteen checks, each over 48 facelets;   *)
(* on the perm side nothing reduces, so this goes through the tables of       *)
(* Sym.v the way mtabsE does.                                                 *)
Lemma moves_cubP m : m \in Sset -> cubP m.
Proof. Admitted.

Lemma cubP_step g m : cubP g -> m \in Sset -> cubP (g * m).
Proof. by move=> cg /moves_cubP cm; exact: cubPM. Qed.

(* an edge facelet stays an edge facelet                                      *)
Lemma cubP_edge g f :
  cubP g -> ((g f : nat) \in eprim ++ esec) = ((f : nat) \in eprim ++ esec).
Proof. Admitted.

(* ---- 5. Bits ------------------------------------------------------------- *)

(* nat indexed bits, because everything above is indexed by a position, and   *)
(* setbit/packn because the summary is built one position at a time.  All     *)
(* three compute: they are shifts and ors, no to_nat anywhere.                *)

Definition nbit (x : int) (k : nat) : bool := bit x (of_nat k).

Definition setbit (x : int) (k : nat) (b : bool) : int :=
  if b then (x lor lsl 1 (of_nat k))%uint63 else x.

Fixpoint packn (k : nat) (f : nat -> bool) : int :=
  if k is k1.+1 then setbit (packn k1 f) k1 (f k1) else 0%uint63.

(* the defining property, and the bound that makes the DfStep loop finite     *)
Lemma nbit_packn k f j : j < k -> k <= ndigits -> nbit (packn k f) j = f j.
Proof. Admitted.

Lemma packn_lt k f : k <= ndigits -> to_nat (packn k f) < 2 ^ k.
Proof. Admitted.

(* two words agreeing on the first k bits are equal, which is how every       *)
(* equation between packed summaries is proved                               *)
Lemma packn_eq k (x y : int) :
  to_nat x < 2 ^ k -> to_nat y < 2 ^ k ->
  (forall j, j < k -> nbit x j = nbit y j) -> x = y.
Proof. Admitted.

(* ---- 6. The summary ------------------------------------------------------ *)

(* The summary is read on g^-1: mathcomp has (g * m) f = m (g f), so the      *)
(* facelet sitting at f is g^-1 f, and the cocycle comes out on that side --  *)
(* the same convention as coordf in Coord.v.                                  *)

(* bit p: the sticker now at the primary facelet of position p is NOT a       *)
(* primary sticker, i.e. the edge at p is flipped                             *)
Definition flipb (g : {perm facelet}) (p : nat) : bool :=
  ~~ pcol (g^-1 (eprimf p)).

(* bit p: the edge now at position p is a slice edge                          *)
Definition sliceb (g : {perm facelet}) (p : nat) : bool :=
  scol (g^-1 (eprimf p)).

Definition ncoord := (nedge + nedge)%N.       (* 24 bits *)

Definition coordfs (g : {perm facelet}) : int :=
  packn ncoord
    (fun k => if k < nedge then flipb g k else sliceb g (k - nedge)).

(* ---- 7. The action ------------------------------------------------------- *)

(* Applying m sends the primary facelet of p to m^-1 (eprimf p), which is a   *)
(* facelet of some position q -- primary or secondary.  Primary and the bit   *)
(* moves unchanged; secondary and the flip bit is complemented, which is      *)
(* exactly xbit.  The slice bit never gets a correction because scol does not *)
(* tell the two facelets of an edge apart.                                    *)

Definition src (m : {perm facelet}) (p : nat) : nat := epos (m^-1 (eprimf p)).

Definition xbit (m : {perm facelet}) (p : nat) : bool :=
  ~~ pcol (m^-1 (eprimf p)).

Definition actfs (x : int) (m : {perm facelet}) : int :=
  packn ncoord
    (fun k => if k < nedge then nbit x (src m k) (+) xbit m k
              else nbit x (nedge + src m (k - nedge))).

(* ---- 8. The three statements this file exists for ------------------------ *)

(* the bound, so that x ranges over a segment of int and DfStep is a loop     *)
Lemma coordfs_lt g : to_nat (coordfs g) < 2 ^ ncoord.
Proof. by apply: packn_lt. Qed.

Lemma actfs_lt x m : to_nat (actfs x m) < 2 ^ ncoord.
Proof. by apply: packn_lt. Qed.

(* THE EQUIVARIANCE.  Both halves reduce to one bit, and one bit to the two   *)
(* cases of edge_case: m^-1 (eprimf p) is eprimf q, and then pcol of it is    *)
(* true so xbit is false and the bit is copied; or it is epair (eprimf q),    *)
(* and then pcol_epair complements the flip bit while scol_epair leaves the   *)
(* slice bit alone.  cubP g is what lets g^-1 be pushed through epair.        *)
Lemma coordfsM g m :
  cubP g -> m \in Sset -> coordfs (g * m) = actfs (coordfs g) m.
Proof. Admitted.

(* ---- 9. What it gives Search.v ------------------------------------------- *)

Section Heuristic.

(* [3c] the table.  Item 3 replaces this by a Definition reading a packed     *)
(* PArray, at which point Dfs0 and DfsStep become two checked computations    *)
(* and this file has no axiom left.                                           *)
Variable Dfs : int -> nat.
Hypothesis Dfs0 : Dfs (coordfs 1) = 0.
Hypothesis DfsStep : forall x m, m \in Sset -> Dfs x <= (Dfs (actfs x m)).+1.

Definition hfs : {perm facelet} -> nat := hcoordg cubP coordfs Dfs.

Lemma hfs0 : hfs 1 = 0.
Proof. by apply: (hcoordg0 cubP1 Dfs0). Qed.

Lemma hfsS g m : m \in Sset -> hfs g <= (hfs (g * m)).+1.
Proof. by apply: (hcoordgS cubP_step coordfsM DfsStep). Qed.

(* and hence the search of Search.v, with no condition on g                   *)
Definition searchfs : nat -> {perm facelet} -> bool := search moves hfs.

Corollary searchfsN d g : searchfs d g = false -> g \notin ball Sset d.
Proof. exact: (@searchN _ moves Sset_inv hfs hfs0 hfsS d g). Qed.

End Heuristic.
