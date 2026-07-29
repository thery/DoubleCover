(* =========================================================================  *)
(*  Coordfsi.v                                                                *)
(*                                                                            *)
(*  The flip x slice summary on the two computable levels, and the two        *)
(*  agreement lemmas that join them to the one on permutations.               *)
(*                                                                            *)
(*  No admits: the three levels agree, and moves_cubP is proved here rather   *)
(*  than in Coordfs.v because it can only be read on the tables.              *)
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

Lemma nfacelet_dig : nfacelet <= ndigits.
Proof. by vm_compute. Qed.

(* what the masks are for: one bit test replaces the membership              *)
Lemma bit_pmask f : f < nfacelet -> nbit pmask f = pcol (inord f).
Proof. by move=> fL; rewrite /pmask nbit_packn ?nfacelet_dig // /pcol inordK. Qed.

Lemma bit_smask f : f < nfacelet -> nbit smask f = scol (inord f).
Proof. by move=> fL; rewrite /smask nbit_packn ?nfacelet_dig // /scol inordK. Qed.

(* the pairing on facelets, read at nat level -- epairn is in Coordfs.v      *)
Lemma epairnE f : f < nfacelet -> epair (inord f) = inord (epairn f).
Proof. by move=> fL; rewrite epairE inordK. Qed.

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

(* The guard is read at every node, so nothing in it may touch nat.  The
   pairing goes into an int array and the loop is indexed by an int: four
   array reads per facelet, where the nat version cost a to_nat, an of_nat
   and two linear scans of a 24 element list.  Measured over 20 000
   evaluations of the heuristic, 55.0 s before and 2.3 s after.            *)

Definition mkarrn (n : int) (l : seq int) : arr :=
  (fix go (a : arr) (i : int) (l : seq int) {struct l} : arr :=
     if l is x :: l' then go (PArray.set a i x) (i + 1)%uint63 l' else a)
    (PArray.make n 0%uint63) 0%uint63 l.

Definition epairi : arr :=
  Eval vm_compute in
  mkarrn (of_nat nfacelet) [seq of_nat (epairn f) | f <- iota 0 nfacelet].

Fixpoint alli (k : nat) (i : int) (f : int -> bool) : bool :=
  if k is k1.+1 then f i && alli k1 (i + 1)%uint63 f else true.

Definition cubti (a : arr) : bool :=
  alli nfacelet 0%uint63
    (fun f => (PArray.get a (PArray.get epairi f) =?
               PArray.get epairi (PArray.get a f))%uint63).

(* ---- 3b. Two bounds and one injectivity ---------------------------------- *)

Lemma epairn_ltn m : m < nfacelet -> epairn m < nfacelet.
Proof.
move=> mL; have [mM|mN] := boolP (m \in eprim ++ esec); first by rewrite epairn_lt.
by rewrite epairnN.
Qed.

Lemma nfacelet_nwB m : m < nfacelet -> m < nwB.
Proof. by move=> mL; apply: leq_trans (leq_trans mL _) n47_small. Qed.

(* inord is injective below the bound, which is how an equation between
   facelets becomes an equation between naturals                             *)
Lemma inord_eq (a b : nat) : a < nfacelet -> b < nfacelet ->
  ((inord a : facelet) == inord b) = (a == b).
Proof.
move=> aL bL; apply/eqP/eqP => [e|->//].
by rewrite -(inordK aL) e inordK.
Qed.

(* the int indexed loop, as a list one -- the same shape as Tabi.v's eqiE *)
Lemma alliE k i (f : int -> bool) :
  to_nat i + k < nwB ->
  alli k i f = all (fun j => f (of_nat j)) (iota (to_nat i) k).
Proof.
elim: k i => [|k IH] i //= hb.
rewrite -[(i + 1)%uint63]/(incr _).
have hi : (to_nat i).+1 < nwB.
  by apply: leq_ltn_trans hb; rewrite addnS ltnS leq_addr.
rewrite IH; last by rewrite to_nat_incr // addSn -addnS.
by rewrite to_nat_incr // to_natK.
Qed.

(* epairi holds what epairn computes.  It is a literal array, so this is 48
   comparisons and not an induction over mkarrn.                           *)
Lemma get_epairi f :
  f < nfacelet -> PArray.get epairi (of_nat f) = of_nat (epairn f).
Proof.
move=> fL; apply: eqb_correct.
apply: (all_iota_lt
  (P := fun f => (PArray.get epairi (of_nat f) =? of_nat (epairn f))%uint63)
  (n := nfacelet)); [by vm_compute | exact: fL].
Qed.

(* ---- 4. Arrays against lists --------------------------------------------- *)

(* Both go the way ti2t_comp does: the summary is a packn over 24 indices,    *)
(* so each reduces to one entry, and one entry is nth_ti2t.  The inverse is   *)
(* already bridged by ti2t_inv.                                               *)

Lemma ecoordiE u : tabi_ok 47 u -> ecoordi u = ecoordt (ti2t 47 u).
Proof.
move=> uok; apply: eq_packn => j jL.
have hnth i : i < nfacelet -> nth 0%N (ti2t 47 u) i = to_nat (PArray.get u (of_nat i)).
  by move=> iL; apply: nth_ti2t.
case: ltnP => jn.
  by rewrite hnth ?eprim_lt // /nbit to_natK.
have hsub : j - nedge < nedge by rewrite -(ltn_add2l nedge) subnKC.
by rewrite hnth ?eprim_lt // /nbit to_natK.
Qed.

Lemma coordiE a : tabi_ok 47 a -> coordi a = coordt (ti2t 47 a).
Proof.
move=> aok; rewrite /coordi /coordt ecoordiE.
  by rewrite (ti2t_inv n47_small n47_len aok).
by rewrite /tabi_ok (ti2t_inv n47_small n47_len aok); apply: tab_ok_inv.
Qed.

Lemma cubtiE a : tabi_ok 47 a -> cubti a = cubt (ti2t 47 a).
Proof.
move=> aok; rewrite /cubti alliE ?to_nat_0 ?add0n //; last exact: n47_small.
rewrite /cubt; apply: eq_in_all => f.
rewrite mem_iota add0n => /andP[_ fL].
rewrite get_epairi // -[X in PArray.get epairi X]to_natK get_epairi;
  last by apply: (tabi_lt aok).
rewrite !(@nth_ti2t 47) ?epairn_ltn //.
have kL : epairn (to_nat (PArray.get a (of_nat f))) < nfacelet.
  by apply: epairn_ltn; apply: (tabi_lt aok).
by rewrite eqb_eqb -(inj_eq to_nat_inj) of_natK ?nfacelet_nwB // eq_sym.
Qed.

(* ---- 5. Lists against permutations --------------------------------------- *)

(* Here the work is ptE and inord: pt t i = inord (nth 0 t i), and pt         *)
(* (inv_tab t) = (pt t)^-1 is ptV, so g^-1 (eprimf p) is inord of an entry of *)
(* the inverse table.  Then bit_pmask and bit_smask turn the two colourings   *)
(* into the two masks and the two sides are the same packn.                   *)

Lemma coordtE t : tab_ok 47 t -> coordfs (pt 47 t) = coordt t.
Proof.
move=> tok; have iok := tab_ok_inv tok.
have ilt p : p < nedge -> nth 0%N (inv_tab 47 t) (nth 0%N eprim p) < nfacelet.
  move=> pL; have /and3P[/eqP sz /allP hall _] := iok.
  by apply: hall; rewrite mem_nth // sz eprim_lt.
have hval p : p < nedge ->
    inord (nth 0%N (inv_tab 47 t) (nth 0%N eprim p)) = (pt 47 t)^-1 (eprimf p).
  by move=> pL; rewrite (ptV tok) ptE // eprimfK.
rewrite /coordfs /coordt /ecoordt; apply: eq_packn => j jL.
have hsub : nedge <= j -> j - nedge < nedge.
  by move=> jn; rewrite -(ltn_add2l nedge) subnKC.
case: ltnP => jn.
  by rewrite /flipb -hval // -bit_pmask ?ilt.
by rewrite /sliceb -hval ?hsub // -bit_smask ?ilt ?hsub.
Qed.

Lemma cubtE t : tab_ok 47 t -> cubP (pt 47 t) = cubt t.
Proof.
move=> tok; have /and3P[/eqP sz /allP hall _] := tok.
have tlt m : m < nfacelet -> nth 0%N t m < nfacelet.
  by move=> mL; apply: hall; rewrite mem_nth // sz.
have key m : m < nfacelet ->
    (epair (pt 47 t (inord m)) == pt 47 t (epair (inord m)))
      = (epairn (nth 0%N t m) == nth 0%N t (epairn m)).
  move=> mL; have elt : epairn m < nfacelet by apply: epairn_ltn.
  rewrite ptE // inordK // epairnE ?tlt // epairnE // ptE // inordK //.
  by rewrite inord_eq ?epairn_ltn ?tlt.
apply/forallP/allP => [h m|h f].
  by rewrite mem_iota add0n => /andP[_ mL]; rewrite -key //; exact: h.
rewrite -(inord_val f) key ?ltn_ord //.
by apply: h; rewrite mem_iota add0n ltn_ord.
Qed.

(* ---- 5b. The guard, on the move set --------------------------------------*)

(* This is why the block below lives here rather than in Coordfs.v: nothing
   about a permutation reduces, so "the eighteen moves keep cubies together"
   has to be read through cubtE, and cubtE is a table fact.                   *)

(* the six faces, each one XmoveT away from a table and then one vm_compute *)
Lemma cubP_faces g : g \in faces -> cubP g.
Proof.
have hf : all cubP faces.
  rewrite /faces /= UmoveT RmoveT FmoveT DmoveT LmoveT BmoveT.
  by rewrite !cubtE; vm_compute.
by move=> gF; apply: (allP hf).
Qed.

Lemma moves_cubP m : m \in Sset -> cubP m.
Proof.
rewrite inE /moves => /flattenP[s /mapP[g gF ->]].
rewrite !inE => /or3P[/eqP->|/eqP->|/eqP->].
- exact: cubP_faces.
- by rewrite expgS expg1; apply: cubPM; exact: cubP_faces.
by apply: cubPV; exact: cubP_faces.
Qed.

Lemma cubP_step g m : cubP g -> m \in Sset -> cubP (g * m).
Proof. by move=> cg /moves_cubP cm; exact: cubPM. Qed.

(* the equivariance, with the moves known to preserve cubies                 *)
Lemma coordfsMS g m :
  cubP g -> m \in Sset -> coordfs (g * m) = actfs (coordfs g) m.
Proof. by move=> cg /moves_cubP cm; apply: coordfsM. Qed.

(* ---- 6. The heuristic at each level, in the shape the searches want ------ *)

Section Heuristic.

(* [3c] the table.  Item 3 replaces this by a Definition reading a packed     *)
(* PArray, and Dfs0/DfsStep by two checked computations.                      *)
Variable Dfs : int -> nat.
Hypothesis Dfs0 : Dfs (coordfs 1) = 0.
Hypothesis DfsStep : forall x m, m \in Sset -> Dfs x <= (Dfs (actfs x m)).+1.

(* what Coordfs.v's summary gives Search.v.  The guard costs nothing: hfs is
   0 off the guarded set, so both conditions come out unconditional.         *)
Definition hfs : {perm facelet} -> nat := hcoordg cubP coordfs Dfs.

Lemma hfs0 : hfs 1 = 0.
Proof. by apply: (hcoordg0 cubP1 Dfs0). Qed.

Lemma hfsS g m : m \in Sset -> hfs g <= (hfs (g * m)).+1.
Proof. by apply: (hcoordgS cubP_step coordfsMS DfsStep). Qed.

Definition searchfs : nat -> {perm facelet} -> bool := search moves hfs.

Corollary searchfsN d g : searchfs d g = false -> g \notin ball Sset d.
Proof. exact: (@searchN _ moves Sset_inv hfs hfs0 hfsS d g). Qed.

(* the guard is re-read at each level rather than carried as an invariant     *)
Definition Dt (t : seq nat) : nat := if cubt t then Dfs (coordt t) else 0.
Definition Dti (a : arr) : nat := if cubti a then Dfs (coordi a) else 0.

(* THE TWO BRIDGES, in exactly the shape searchtE and searchiE ask for.       *)
Lemma hfsE t : tab_ok 47 t -> hfs (pt 47 t) = Dt t.
Proof. by move=> tok; rewrite /hfs /hcoordg /Dt cubtE // coordtE. Qed.

Lemma DtiE a : tabi_ok 47 a -> Dti a = Dt (ti2t 47 a).
Proof. by move=> aok; rewrite /Dti /Dt cubtiE // coordiE. Qed.

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
move=> aok sE; apply: (searchfsN (d := d)).
rewrite /searchfs mtisE.
by apply: (searchiN n47_small n47_len mtis_ok DtiE hfsE aok sE).
Qed.

End Heuristic.
