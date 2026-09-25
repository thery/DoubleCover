(* =========================================================================  *)
(*  RowFoldFinalC.v -- RowFoldFinal's fmfino over the run of RowFoldRunC:    *)
(*  the prepass only when the cuts are on, as the OCaml.                     *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Root Coord.
Require Import Diameter Moves Sym16 Sym16Row.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembChk.
Require Import RowFold RowFoldOk RowFoldMem RowFoldPart.
Require Import RowTabF RowFoldTab RowFoldSym RowFoldConj RowFoldGath RowFoldSrc.
Require Import RowFoldLvl RowFoldWrite RowFoldTot RowFoldPorb.
Require Import RowFoldSrch RowFoldRun RowFoldEmpty RowFoldFinal RowFoldRunC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* where a member of the row stands, as RowInst.posE writes it out *)
Definition posC (x : memb) : {perm facelet} :=
  superflip^-1 * pt flast (memb2tab x).

Section FFinalC.

(* ---- the folded phase one table, which nothing here reads ---------------- *)

Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

(* ---- what the search carries, and the five things it owes ---------------- *)

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable posp : pst -> {perm facelet}.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch nlev : nat.

Variable coordP : int -> pst -> Prop.
Variable pstok : pst -> bool.

Hypothesis coord_root : coordP croot sroot.
Hypothesis root_ball : posp sroot \in ball Sset 0.
Hypothesis root_pok : pstok sroot.
Hypothesis coord_step : forall c x k, (to_nat k < RowRun.nmvn)%N -> pstok x ->
  coordP c x -> coordP (cstep c k) (xstep x k).
Hypothesis xstep_pok : forall x k, (to_nat k < RowRun.nmvn)%N ->
  pstok x -> pstok (xstep x k).
Hypothesis xstep_pos : forall x k, (to_nat k < RowRun.nmvn)%N -> pstok x ->
  posp (xstep x k) = posp x * nth 1%g moves (to_nat k).
Hypothesis leaf_memb : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> membok par8i par4i (tomemb x).
Hypothesis leaf_pos : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> posC (tomemb x) = posp x.

Variables forb fpop : arr.
Variable ishm : int.

Definition fmfinoC : rmap :=
  frunskc e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          F frep fsym twsym dnlo dnhi fllo flhi
          cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm
          nlev 0 0%uint63 (mkempty tt) (mkempty tt).

Lemma fmfinoC_sound : soundatf fpgi fsgri fsbti (PdC nlev) fmfinoC.
Proof.
rewrite /fmfinoC -{1}[nlev]add0n.
refine (@frunskc_sound e8numi e8invi e4biti e4ofi par8i par4i e8okC e4okC
          fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti mgri mswi mloi mhii
          F frep fsym twsym dnlo dnhi fllo flhi
          pst cstep xstep tomemb posp okmv csolved croot sroot dsrch
          posC _ _ _ coordP pstok _ _ _ _ _ _ _ _ forb fpop ishm
          nlev 0 0%uint63 (mkempty tt) (mkempty tt) _ _ _ _).
- exact: PorbC.
- exact: QloC.
- exact: QhiC.
- exact: coord_root.
- exact: root_ball.
- exact: root_pok.
- exact: coord_step.
- exact: xstep_pok.
- exact: xstep_pos.
- exact: leaf_memb.
- exact: leaf_pos.
- exact: pchk_mkemptyf.
- exact: pchk_mkemptyf.
- exact: soundatf_mkemptyf.
exact: soundatf_mkemptyf.
Qed.

End FFinalC.
