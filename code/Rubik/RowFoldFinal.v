(* =========================================================================  *)
(*  RowFoldFinal.v -- the map the folded run leaves.                          *)
(* =========================================================================  *)

(* fmfin and fmfino, unoptimized and optimized, with their soundness.  What   *)
(* is about the fold is discharged here; what is about the cube stays a       *)
(* hypothesis, and RowCubInst supplies it.                                    *)

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
Require Import RowFoldSrch RowFoldRun RowFoldEmpty.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* where a member of the row stands, as RowInst.posE writes it out *)
Definition posC (x : memb) : {perm facelet} :=
  superflip^-1 * pt flast (memb2tab x).

Section FFinal.

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

(* ---- the map the run leaves ---------------------------------------------- *)

(* two maps, allocated once and swapped at every level                        *)
Definition fmfin : rmap :=
  frun e8numi e4biti fpgi fsrci fsgri fsloi fshii fsbti mgri mswi mloi mhii
       F frep fsym twsym dnlo dnhi fllo flhi
       cstep xstep tomemb okmv csolved croot sroot dsrch nlev 0
       (mkempty tt) (mkempty tt).

Lemma fmfin_sound : soundatf fpgi fsgri fsbti (PdC nlev) fmfin.
Proof.
rewrite /fmfin -{1}[nlev]add0n.
(* refine, not exact: every one of the fifty eight arguments is named here,  *)
(* and exact's unification will not take pos on trust.                       *)
refine (@frun_sound e8numi e8invi e4biti e4ofi par8i par4i e8okC e4okC
          fpgi fsrci fsgri fsloi fshii fsbti mgri mswi mloi mhii
          F frep fsym twsym dnlo dnhi fllo flhi
          pst cstep xstep tomemb posp okmv csolved croot sroot dsrch
          posC _ _ _ coordP pstok _ _ _ _ _ _ _ _ nlev 0
          (mkempty tt) (mkempty tt) _ _ _ _).
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

(* ---- so a full folded map puts every member within the depth ------------- *)

Lemma fmfin_all : mfullf fmfin ->
  forall pg gr bt, inrange pg gr bt -> PdC nlev pg gr bt.
Proof.
move=> hm.
refine (@foldf_all fpgi fsgri fsbti (PdC nlev) fkptT
          (fun pg' gr' bt' => sgrmvT _ _ _) (fun pg' bt' => sbtmvT _ _)
          fmfin hm fmfin_sound).
Qed.

(* ---- and a witness can be marked into it, instead of held in a map ------- *)

(* THE WITNESSES NEED NO MAP OF THEIR OWN.  The plain row keeps them in a     *)
(* second, whole map and asks mfull2 of the two -- which allocates a map the  *)
(* size of the first for thirty two bits, and reads both at every word.       *)
(* Marking them into the map the run leaves does the same work: the map is    *)
(* already sound at the depth, a witness is a member within that depth, and   *)
(* soundatf_fmark says the mark keeps it sound.  Then mfullf alone is the     *)
(* test.                                                                      *)
(*                                                                            *)
(* IT HAS TO BE AT THE END AND NOT AT THE START.  A map sound at d claims     *)
(* every bit it has set is within d; a witness is within TWENTY, so seeding   *)
(* it before the run would make the first level claim its neighbours are      *)
(* within one, and they are not.                                             *)
Lemma fmark_sound m pg gr bt :
  inrange pg gr bt -> PdC nlev pg gr bt ->
  soundatf fpgi fsgri fsbti (PdC nlev) m ->
  soundatf fpgi fsgri fsbti (PdC nlev) (fmark fpgi fsgri fsbti m pg gr bt).
Proof. exact: (soundatf_fmark (@PorbC nlev)). Qed.

(* =========================================================================  *)
(*  The same, with every optimization on.                                     *)
(* =========================================================================  *)

(* fmfin runs the plain level.  This runs flvlsk -- Rokicki's early stop and  *)
(* hcoset's two cuts -- which RowFoldRun proves sound, so the certificate may *)
(* use it.  The cuts come on when the row passes six million members, which   *)
(* is the prototype's own rule and is what n0 carries.                        *)

Variables forb fpop : arr.
Variable ishm : int.

Definition fmfino : rmap :=
  frunsk e8numi e4biti fpgi fsrci fsgri fsloi fshii fsbti mgri mswi mloi mhii
         F frep fsym twsym dnlo dnhi fllo flhi
         cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm
         nlev 0 0%uint63 (mkempty tt) (mkempty tt).

Lemma fmfino_sound : soundatf fpgi fsgri fsbti (PdC nlev) fmfino.
Proof.
rewrite /fmfino -{1}[nlev]add0n.
refine (@frunsk_sound e8numi e8invi e4biti e4ofi par8i par4i e8okC e4okC
          fpgi fsrci fsgri fsloi fshii fsbti mgri mswi mloi mhii
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

Lemma fmfino_all : mfullf fmfino ->
  forall pg gr bt, inrange pg gr bt -> PdC nlev pg gr bt.
Proof.
move=> hm.
refine (@foldf_all fpgi fsgri fsbti (PdC nlev) fkptT
          (fun pg' gr' bt' => sgrmvT _ _ _) (fun pg' bt' => sbtmvT _ _)
          fmfino hm fmfino_sound).
Qed.

End FFinal.
