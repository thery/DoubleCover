(* =========================================================================  *)
(*  RowFoldRunC.v -- the folded level as the OCaml runs it: the prepass only  *)
(*  when the cuts are on.                                                     *)
(* =========================================================================  *)

(* rubik_row_fold.ml, and hcoset before it, run the prepass on a level only   *)
(* when the cuts are on: `if !cut then carry () else blitmaps ()`.  Below the *)
(* six million threshold the search at that level is complete, so the map it *)
(* reads needs nothing from the moves of H.  RowFoldSrch's flvlsk runs the    *)
(* prepass at every level; to depth thirteen that is thirteen passes over the *)
(* map for nothing, 123 s of a 295 s run, measured.                           *)
(*                                                                            *)
(* HERE: the level searches the map as it is when the cuts are off.  A map    *)
(* sound at d is sound at d + 1, so nothing new is proved about the cube:     *)
(* the search lemmas of RowFoldRun carry over, only the map they start from   *)
(* changes.  With the cuts off the destination map is not written, so it is   *)
(* handed on untouched to the next level.                                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask.
Require Import RowFold RowFoldOk RowFoldLvl RowFoldSrch RowFoldRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FRunC.

(* ---- the layout, from Row.v ---------------------------------------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place24 e8num e4bit).
Local Notation unplc := (unplace24 e8inv e4of par8 par4).

(* ---- the fold, and the move on groups and bits --------------------------- *)

Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.

Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
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
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

Local Notation fsr :=
  (fsrch e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved).
Local Notation flv :=
  (flvl e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch).
Local Notation frn :=
  (frun e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch).

(* ---- what the map claims, and what a member is --------------------------- *)

Variable pos : memb -> {perm facelet}.

Local Notation Pd := (Pd e8inv e4of par8 par4 pos).
Local Notation soundatd := (soundatd e8inv e4of par8 par4 fpg fsgr fsbt pos).

Hypothesis Porbd : forall d, forall p q c pg gr bt,
  inrange24 p q c -> inrange24 pg gr bt ->
  pchk (fkpt (PArray.get fpg p)) = pchk (fkpt (PArray.get fpg pg)) ->
  Uint63.add (poff (fkpt (PArray.get fpg p)))
    (sgrmv fsgr (fren (PArray.get fpg p))
       (fpar (PArray.get fpg p) lxor (if c <? 12 then 0 else 1)) q)
  = Uint63.add (poff (fkpt (PArray.get fpg pg)))
      (sgrmv fsgr (fren (PArray.get fpg pg))
         (fpar (PArray.get fpg pg) lxor (if bt <? 12 then 0 else 1)) gr) ->
  ~~ (Uint63.land (bitof (fbit (fhlf (PArray.get fpg p))
                     (sbtmv fsbt (fren (PArray.get fpg p)) c)))
                  (bitof (fbit (fhlf (PArray.get fpg pg))
                     (sbtmv fsbt (fren (PArray.get fpg pg)) bt))) =? 0) ->
  Pd d p q c -> Pd d pg gr bt.

Hypothesis Qlod : forall d,
  Qlo_st fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi (Pd d) (Pd d.+1).
Hypothesis Qhid : forall d,
  Qhi_st fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi (Pd d) (Pd d.+1).

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
  posp x \in G -> csolved c -> membok par8 par4 (tomemb x).
Hypothesis leaf_pos : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> pos (tomemb x) = posp x.

(* ---- the search does not change how long the map is ---------------------- *)

Variables forb fpop : arr.
Variable ishm : int.

Local Notation fsrk :=
  (fsrchk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation fsrsk :=
  (fsrchsk e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).
Local Notation flvsk :=
  (flvlsk e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm).
Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).

(* ---- hcoset's last level ------------------------------------------------- *)

(* AT THE LAST MOVE THE CHILD IS A LEAF, and a leaf is the search at depth    *)
(* nought: the solved test and the mark, no table read.  So the child is      *)
(* handed straight to fsrk at nought, where the search would first read the   *)
(* table and decode a mask to test a depth that is already known.  hcoset     *)
(* does the same (its togo == 1 branch).  Soundness is fsrchk_sound at       *)
(* nought, so nothing about the cube is proved twice.                        *)
Fixpoint fsrchkL (cut : bool) (togo : nat) (c : int) (x : pst) (msk pv : int)
                 (m : rmap) : rmap :=
  if togo is togo'.+1 then
    if togo' is 0 then
      ifold RowRun.nmvn 0
        (fun k m' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
           else if ~~ okmv pv k then m'
           else if cut && ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
           then m'
           else fsrk cut 0 (cstep c k) (xstep x k) 0 k m')
        m
    else
    ifold RowRun.nmvn 0
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
         else if ~~ okmv pv k then m'
         else if [&& cut, (togo' == 0)%N
                  & ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0]
         then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if [&& (nd <= togo')%N
               & [|| ~~ cut, (nd == togo')%N | (rcuti <= togo' + nd)%N]]
           then fsrchkL cut togo' c' (xstep x k) (wmask w (togo' - nd)) k m'
           else m')
      m
  else fsrk cut 0 c x msk pv m.

(* the counting search, the same way                                          *)
Fixpoint fsrchskL (cut : bool) (togo : nat) (c : int) (x : pst) (msk pv : int)
                  (enough : int) (mn : rmap * int) : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    if togo' is 0 then
      ifold RowRun.nmvn 0
        (fun k a =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
           else if ~~ okmv pv k then a
           else if cut && ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
           then a
           else fsrsk cut 0 (cstep c k) (xstep x k) 0 k enough a)
        mn
    else
    ifold RowRun.nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmv pv k then a
         else if [&& cut, (togo' == 0)%N
                  & ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0]
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if [&& (nd <= togo')%N
               & [|| ~~ cut, (nd == togo')%N | (rcuti <= togo' + nd)%N]]
           then fsrchskL cut togo' c' (xstep x k) (wmask w (togo' - nd)) k
                         enough a
           else a)
      mn
  else fsrsk cut 0 c x msk pv enough mn.

Lemma fsrchkL_len cut togo c x msk pv m :
  PArray.length (fsrchkL cut togo c x msk pv m) = PArray.length m.
Proof.
elim: togo c x msk pv m => [|togo ih] c x msk pv m; first exact: fsrchk_len.
case: togo ih => [|togo] ih.
  apply: (@ifold_indi _ (fun m' => PArray.length m' = PArray.length m));
      [by apply: ltnW; apply: (@ltn_nwB 5)| |by []].
  move=> k m' hk hl.
  case: ifP => _; first exact: hl.
  case: ifP => _; first exact: hl.
  case: ifP => _; first exact: hl.
  by rewrite fsrchk_len.
apply: (@ifold_indi _ (fun m' => PArray.length m' = PArray.length m));
    [by apply: ltnW; apply: (@ltn_nwB 5)| |by []].
move=> k m' hk hl.
case: ifP => _; first exact: hl.
case: ifP => _; first exact: hl.
case: ifP => _; first exact: hl.
cbv zeta; case: ifP => _; last exact: hl.
by rewrite ih; exact: hl.
Qed.

Lemma fsrchskL_len cut togo c x msk pv enough mn :
  PArray.length (fsrchskL cut togo c x msk pv enough mn).1
  = PArray.length mn.1.
Proof.
elim: togo c x msk pv mn => [|togo ih] c x msk pv mn.
  rewrite /fsrchskL; case: ifP => _; first by [].
  exact: fsrchsk_len.
rewrite /fsrchskL -/fsrchskL; case: ifP => _; first by [].
case: togo ih => [|togo] ih.
  apply: (@ifold_indi _ (fun a => PArray.length a.1 = PArray.length mn.1));
      [by apply: ltnW; apply: (@ltn_nwB 5)| |by []].
  move=> k a hk hl.
  case: ifP => _; first exact: hl.
  case: ifP => _; first exact: hl.
  case: ifP => _; first exact: hl.
  by rewrite fsrchsk_len.
apply: (@ifold_indi _ (fun a => PArray.length a.1 = PArray.length mn.1));
    [by apply: ltnW; apply: (@ltn_nwB 5)| |by []].
move=> k a hk hl.
case: ifP => _; first exact: hl.
case: ifP => _; first exact: hl.
case: ifP => _; first exact: hl.
cbv zeta; case: ifP => _; last exact: hl.
by rewrite ih; exact: hl.
Qed.

(* the child of the last move is in the ball of the level                     *)
Lemma lastL_ball x k d : (to_nat k < RowRun.nmvn)%N -> pstok x -> (1 <= d)%N ->
  posp x \in ball Sset (d - 1) -> posp (xstep x k) \in ball Sset (d - 0).
Proof.
move=> hk hp hd hb; rewrite (xstep_pos hk hp) subn0 -(subnK hd) addn1.
by apply: ball_step; [exact: hb | apply: mv_Sset; exact: hk].
Qed.

Lemma fsrchkL_sound cut togo c x msk pv m d :
  (togo <= d)%N -> coordP c x -> pstok x ->
  soundatd m d -> posp x \in ball Sset (d - togo) ->
  soundatd (fsrchkL cut togo c x msk pv m) d.
Proof.
elim: togo c x msk pv m => [|togo ih] c x msk pv m hdt hc hp hm hb.
  apply: fsrchk_sound; try eassumption.
case: togo ih hdt hb => [|togo] ih hdt hb.
  apply: (@ifold_indi _ (fun m' => soundatd m' d)); [| |exact: hm].
    by apply: ltnW; apply: (@ltn_nwB 5).
  move=> k m' hk hm'.
  case: ifP => _; first exact: hm'.
  case: ifP => _; first exact: hm'.
  case: ifP => _; first exact: hm'.
  apply: fsrchk_sound; try eassumption.
  - exact: leq0n.
  - exact: coord_step.
  - exact: xstep_pok.
  exact: lastL_ball.
apply: (@ifold_indi _ (fun m' => soundatd m' d)); [| |exact: hm].
  by apply: ltnW; apply: (@ltn_nwB 5).
move=> k m' hk hm'.
case: ifP => _; first exact: hm'.
case: ifP => _; first exact: hm'.
case: ifP => _; first exact: hm'.
cbv zeta; case: ifP => hle; last exact: hm'.
apply: (ih _ _ _ _ _ _ (coord_step hk hp hc) (xstep_pok hk hp) hm');
    first by apply: ltnW.
rewrite (xstep_pos hk hp) -(subnSK hdt).
by apply: ball_step; [exact: hb | apply: mv_Sset; exact: hk].
Qed.

Lemma fsrchskL_sound cut togo c x msk pv enough mn d :
  (togo <= d)%N -> coordP c x -> pstok x ->
  soundatd mn.1 d -> posp x \in ball Sset (d - togo) ->
  soundatd (fsrchskL cut togo c x msk pv enough mn).1 d.
Proof.
elim: togo c x msk pv mn => [|togo ih] c x msk pv mn hdt hc hp hm hb.
  rewrite /fsrchskL; case: ifP => _; first exact: hm.
  apply: fsrchsk_sound; try eassumption.
rewrite /fsrchskL -/fsrchskL; case: ifP => _; first exact: hm.
case: togo ih hdt hb => [|togo] ih hdt hb.
  apply: (@ifold_indi _ (fun a => soundatd a.1 d)); [| |exact: hm].
    by apply: ltnW; apply: (@ltn_nwB 5).
  move=> k a hk ha.
  case: ifP => _; first exact: ha.
  case: ifP => _; first exact: ha.
  case: ifP => _; first exact: ha.
  apply: fsrchsk_sound; try eassumption.
  - exact: leq0n.
  - exact: coord_step.
  - exact: xstep_pok.
  exact: lastL_ball.
apply: (@ifold_indi _ (fun a => soundatd a.1 d)); [| |exact: hm].
  by apply: ltnW; apply: (@ltn_nwB 5).
move=> k a hk ha.
case: ifP => _; first exact: ha.
case: ifP => _; first exact: ha.
case: ifP => _; first exact: ha.
cbv zeta; case: ifP => hle; last exact: ha.
apply: (ih _ _ _ _ _ _ (coord_step hk hp hc) (xstep_pok hk hp) ha);
    first by apply: ltnW.
rewrite (xstep_pos hk hp) -(subnSK hdt).
by apply: ball_step; [exact: hb | apply: mv_Sset; exact: hk].
Qed.

(* ---- the level with no prepass ------------------------------------------- *)

(* flvlsk's body with the map it searches given, instead of made by flev, *)
(* and the searches with the last level                                    *)
Definition fslvsk (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (fsrchskL cut d croot sroot (wmask w (d - nd)) 18%uint63 e (m', n0)).1
      else fsrchkL cut d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

(* THE RUN, AS THE OCAML: cuts on, prepass then search, and the old map is   *)
(* the next destination; cuts off, search the map as it is, and the          *)
(* destination, not written, stays the destination.                          *)
Fixpoint frunskc (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := fslvsk true d.+1 (flev m dst) in
      frunskc n1 d.+1 (fcount forb fpop m') m' m
    else
      let m' := fslvsk false d.+1 m in
      frunskc n1 d.+1 (fcount forb fpop m') m' dst
  else m.

Lemma fslvsk_len cut d m : PArray.length (fslvsk cut d m) = PArray.length m.
Proof.
rewrite /fslvsk; cbv zeta.
case: ifP => _; last by [].
case: ifP => _; last by [].
case: ifP => _.
  by rewrite fsrchskL_len.
by rewrite fsrchkL_len.
Qed.

Lemma fslvsk_sound cut m d :
  soundatd m d.+1 -> soundatd (fslvsk cut d.+1 m) d.+1.
Proof.
move=> hg; rewrite /fslvsk; cbv zeta.
case: ifP => _; last exact: hg.
case: ifP => _; last exact: hg.
case: ifP => _; last first.
  apply: fsrchkL_sound; try eassumption; first exact: leqnn.
  by rewrite subnn; exact: root_ball.
apply: fsrchskL_sound; try eassumption; first exact: leqnn.
by rewrite subnn; exact: root_ball.
Qed.

Lemma frunskc_sound n d n0 m dst :
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length m)) ->
  (forall r, (to_nat r < nrepn)%N -> (pchk r <? PArray.length dst)) ->
  soundatd m d -> soundatd dst d -> soundatd (frunskc n d n0 m dst) (d + n).
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hlm hld hm hd.
  by rewrite addn0; exact: hm.
rewrite addnS -addSn /= -/frunskc; case: ifP => _.
  apply: ih.
  - by move=> r hr; rewrite fslvsk_len flevel_length; apply: hld.
  - exact: hlm.
  - apply: fslvsk_sound; rewrite /soundatd; apply: flevel_sound.
    + exact: Qlod.
    + exact: Qhid.
    + exact: PdW.
    + exact: hld.
    + exact: hm.
    exact: soundatdW.
  exact: soundatdW.
apply: ih.
- by move=> r hr; rewrite fslvsk_len; apply: hlm.
- exact: hld.
- by apply: fslvsk_sound; exact: soundatdW.
exact: soundatdW.
Qed.

End FRunC.
