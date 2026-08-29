(* =========================================================================  *)
(*  RowFoldRun.v -- the folded search, and the folded run, are sound.         *)
(* =========================================================================  *)

(* RowRun.v proves the plain search and the plain run sound.  This file does  *)
(* the same for the folded ones, and the two halves it needs are done:        *)
(*                                                                            *)
(* THE GATHER is RowFoldLvl.flevel_sound, on the two write obligations that   *)
(* RowFoldWrite.QloC and QhiC discharge.                                      *)
(*                                                                            *)
(* THE SEARCH is here, and it is RowRun.srch_sound mark for mark -- with one  *)
(* simplification.  The plain leaf has to say what a mark does to a map that  *)
(* is read at a different place; the folded one does not, because             *)
(* RowFoldOk.soundatf_fmark already carries that in Porb.  So the leaf is     *)
(* three lines instead of eight.                                              *)
(*                                                                            *)
(* THE PHASE ONE TABLE IS NEVER TRUSTED HERE EITHER.  The distance and the    *)
(* mask are numbers the search tests and nothing more -- a cut that loses     *)
(* words can only make the row finish later, never call a member covered      *)
(* when it is not -- so nothing in this file says what the folded table is.   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask.
Require Import RowFold RowFoldOk RowFoldLvl RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FRun.

(* ---- the layout, from Row.v ---------------------------------------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).

(* ---- the fold, and the move on groups and bits --------------------------- *)

Variable fpg fsrc fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.

Local Notation flev := (flevel fsrc fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).

(* ---- the folded phase one table, which nothing here reads ---------------- *)

Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

(* ---- what the search carries --------------------------------------------- *)

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable posp : pst -> {perm facelet}.
Variable okmv : int -> int -> bool.
Variable csolved : int -> pst -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

Local Notation fsr :=
  (fsrch e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved).
Local Notation flv :=
  (flvl e8num e4bit fpg fsrc fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch).
Local Notation frn :=
  (frun e8num e4bit fpg fsrc fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch).

(* ---- what the map claims, and what a member is --------------------------- *)

Variable pos : memb -> {perm facelet}.

Definition Pd (d : nat) (pg gr bt : int) : Prop :=
  pos (unplc pg gr bt) \in ball Sset d.

Definition soundatd (m : rmap) (d : nat) : Prop :=
  soundatf fpg fsgr fsbt (Pd d) m.

Lemma PdW d pg gr bt : Pd d pg gr bt -> Pd d.+1 pg gr bt.
Proof. by apply: (subsetP (ball_mono Sset d)). Qed.

Lemma soundatdW m d : soundatd m d -> soundatd m d.+1.
Proof. by move=> h pg gr bt hr ht; apply: PdW; apply: (h _ _ _ hr ht). Qed.

(* ---- the three things the fold owes, and RowFoldWrite has them ----------- *)

Hypothesis Porbd : forall d, forall p q c pg gr bt,
  inrange p q c -> inrange pg gr bt ->
  pchk (fkpt (PArray.get fpg p)) = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff (fkpt (PArray.get fpg p)))
    (sgrmv fsgr (fren (PArray.get fpg p))
       (fpar (PArray.get fpg p) lxor (if c <? 12 then 0 else 1)) q)
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
      (sgrmv fsgr (fren (PArray.get fpg pg))
         (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
  ~~ (Uint63.land (bitof (sbtmv fsbt (fren (PArray.get fpg p)) c))
                  (bitof (sbtmv fsbt (fren (PArray.get fpg pg)) bt)) =? 0) ->
  Pd d p q c -> Pd d pg gr bt.

Hypothesis Qlod : forall d,
  Qlo_st fpg fsrc fsgr fslo fshi fsbt mgr msw mlo mhi (Pd d) (Pd d.+1).
Hypothesis Qhid : forall d,
  Qhi_st fpg fsrc fsgr fslo fshi fsbt mgr msw mlo mhi (Pd d) (Pd d.+1).

(* ---- and the five the search owes, which are RowRun's own ---------------- *)

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
  posp (xstep x k) = (posp x * nth 1%g moves (to_nat k))%g.
Hypothesis leaf_memb : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c x -> membok par8 par4 (tomemb x).
Hypothesis leaf_pos : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c x -> pos (tomemb x) = posp x.

(* ---- the search does not change how long the map is ---------------------- *)

Lemma fmark_len m p q c : PArray.length (fmk m p q c) = PArray.length m.
Proof. by rewrite /fmark /ffor /fset RowMap.length_setA. Qed.

Lemma fsrch_len togo c x msk pv m :
  PArray.length (fsr togo c x msk pv m) = PArray.length m.
Proof.
(* NO `/=' ON THE STEP.  It unfolds the eighteen way ifold and reaches into *)
(* the tables; the branches are taken one at a time instead.                 *)
elim: togo c x msk pv m => [|togo ih] c x msk pv m.
  rewrite /=; case: ifP => _; last by [].
  by case: (plc (tomemb x)) => [[pg gr] bt]; exact: fmark_len.
apply: (@ifold_indi _ (fun m' => PArray.length m' = PArray.length m));
    [by apply: ltnW; apply: (@ltn_nwB 5)| |by []].
move=> k m' hk hl.
case: ifP => _; first exact: hl.
case: ifP => _; first exact: hl.
cbv zeta; case: ifP => _; last exact: hl.
by rewrite ih; exact: hl.
Qed.

Lemma flvl_len d m dst : PArray.length (flv d m dst) = PArray.length dst.
Proof.
rewrite /flvl; cbv zeta.
case: ifP => _; last exact: flevel_length.
case: ifP => _; last exact: flevel_length.
by rewrite fsrch_len; exact: flevel_length.
Qed.

(* THE LEAF, RESTATED.  `/=' takes the mark apart as well as the triple, and *)
(* soundatf_fmark is about the mark; read through this equation -- which is  *)
(* reflexivity -- the mark is still there to match.                          *)
Lemma fsrch0 c x msk pv m :
  fsr 0 c x msk pv m =
  (if csolved c x
   then fmk m (mcp (tomemb x))
            (Uint63.div (PArray.get e8num (mud (tomemb x))) 2%uint63)
            (PArray.get e4bit (mmp (tomemb x)))
   else m).
Proof. by []. Qed.

(* ---- THE SEARCH.  RowRun.srch_sound, with a shorter leaf ----------------- *)

(* A bit the search sets is a member of the row reached by the word it        *)
(* played.  An induction on the word and nothing more: the search is never    *)
(* asked to have found everything, which is the half a lower bound cannot do  *)
(* without.  The cuts, the mask and the redundancy rule never enter it.       *)
Lemma fsrch_sound togo c x msk pv m d :
  (togo <= d)%N -> coordP c x -> pstok x ->
  soundatd m d -> posp x \in ball Sset (d - togo) ->
  soundatd (fsr togo c x msk pv m) d.
Proof.
elim: togo c x msk pv m => [|togo ih] c x msk pv m hdt hc hp hm hb.
  (* a leaf: the position is in H and the three ranks are the member it is *)
  have hG : posp x \in G := subsetP (ball_sub_gen Sset _) _ hb.
  have E : plc (tomemb x) =
      (mcp (tomemb x),
       Uint63.div (PArray.get e8num (mud (tomemb x))) 2%uint63,
       PArray.get e4bit (mmp (tomemb x))) by [].
  rewrite fsrch0; case: ifP => [hs|_]; last exact: hm.
  have hok := leaf_memb hc hp hG hs.
  (* soundatd is named, so it has to be unfolded for apply to see through *)
  rewrite /soundatd; apply: soundatf_fmark.
  - exact: Porbd.
  - exact: (place_range he8 he4 hok E).
  - rewrite /Pd (unplace_place he8 he4 hok E) (leaf_pos hc hp hG hs).
    by move: hb; rewrite subn0.
  exact: hm.
(* a step: the same map, one move further out *)
apply: (@ifold_indi _ (fun m' => soundatd m' d)); [| |exact: hm].
  by apply: ltnW; apply: (@ltn_nwB 5).
move=> k m' hk hm'.
case: ifP => _; first exact: hm'.
case: ifP => _; first exact: hm'.
cbv zeta; case: ifP => hle; last exact: hm'.
apply: (ih _ _ _ _ _ _ (coord_step hk hp hc) (xstep_pok hk hp) hm');
    first by apply: ltnW.
rewrite (xstep_pos hk hp) -(subnSK hdt).
by apply: ball_step; [exact: hb | apply: mv_Sset; exact: hk].
Qed.

(* ---- one level: the gather, then the search ------------------------------ *)

Lemma flvl_sound m dst d :
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length dst)) ->
  soundatd m d -> soundatd dst d.+1 -> soundatd (flv d.+1 m dst) d.+1.
Proof.
move=> hlen hm hd; rewrite /flvl; cbv zeta.
have hg : soundatd (flev m dst) d.+1.
  rewrite /soundatd; apply: flevel_sound.
  - exact: Qlod.
  - exact: Qhid.
  - exact: PdW.
  - exact: hlen.
  - exact: hm.
  exact: hd.
case: ifP => _; last exact: hg.
case: ifP => _; last exact: hg.
apply: (fsrch_sound _ coord_root root_pok hg) => //.
by rewrite subnn.
Qed.

(* ---- and the run, which is the levels one after another ------------------ *)

Lemma frun_sound n d m dst :
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length m)) ->
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length dst)) ->
  soundatd m d -> soundatd dst d -> soundatd (frn n d m dst) (d + n).
Proof.
elim: n d m dst => [|n ih] d m dst hlm hld hm hd /=; first by rewrite addn0.
rewrite addnS -addSn.
apply: ih => //.
- by move=> r hr; rewrite flvl_len; apply: hld.
- by apply: flvl_sound => //; apply: soundatdW.
by apply: soundatdW.
Qed.

End FRun.
