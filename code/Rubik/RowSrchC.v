(* =========================================================================  *)
(*  RowSrchC.v -- the plain level as the OCaml runs it: the prepass only when *)
(*  the cuts are on.                                                          *)
(* =========================================================================  *)

(* RowFoldRunC's change on the plain map.  levelsk runs the prepass at every  *)
(* level; the OCaml (`if !cut then carry () else blitmaps ()`) and hcoset run *)
(* it only when the cuts are on, since below six million members the search   *)
(* at that level is complete.  With the cuts off the level searches the map   *)
(* as it is and the destination, not written, is handed on.  A map sound at d *)
(* is sound at d + 1, so the search lemmas of RowSrchP carry over.            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask RowSrch RowSrchP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section SrchC.

(* ---- the layout, the prepass and the table: RowRun's own ----------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).

Variable cpg cfl mgr msw mlo mhi : arr.

(* THE PREPASS IS A PARAMETER.  RowMap's is one; RowLvl's prepassD, which     *)
(* reads each page's chunk once and puts it back once, is another and is      *)
(* proved equal to it.  The run takes whichever it is handed.  The proof asks *)
(* only that it be RowMap's.                                                  *)
Variable prep : rmap -> rmap -> rmap.

Hypothesis prep_eq : forall m dst,
  prep m dst = prepass cpg cfl mgr msw mlo mhi m dst.

(* ---- the phase one table, folded, and the moves it names ----------------- *)

(* THE OTHER FOLD, AND IT IS NOT THE MAP'S.  Rokicki folds the phase one      *)
(* table by the sixteen symmetries and stores one rank of each orbit; beside  *)
(* the distance an entry names which moves bring the state nearer H and which *)
(* at least do not take it further.  A node then offers three or four moves   *)
(* where RowRun's table left it offering eighteen.                            *)
(*                                                                            *)
(* THIS IS THE SAME READ THE FOLDED RUN MAKES.  Only the MAP is unfolded      *)
(* here; the table is folded on both sides, because that fold costs the run   *)
(* nothing and is what makes the search finish.                               *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).
Local Notation nmvn := RowRun.nmvn.

(* ---- what the search carries: RowRun's own ------------------------------- *)

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

(* the moves of H, one bit each                                               *)
Variable ishm : int.

Local Notation p1g := (sp1g F frep fsym twsym).
Local Notation srchk := (RowSrch.srchk e8num e4bit F frep fsym twsym
                           dnlo dnhi fllo flhi cstep xstep tomemb okmv
                           csolved ishm).
Local Notation srchsk := (RowSrch.srchsk e8num e4bit F frep fsym twsym
                            dnlo dnhi fllo flhi cstep xstep tomemb okmv
                            csolved ishm).
Local Notation levelsk := (RowSrch.levelsk e8num e4bit prep
                             F frep fsym twsym dnlo dnhi fllo flhi
                             cstep xstep tomemb okmv csolved croot sroot
                             dsrch ishm).
Local Notation runsk := (RowSrch.runsk e8num e4bit prep
                           F frep fsym twsym dnlo dnhi fllo flhi
                           cstep xstep tomemb okmv csolved croot sroot
                           dsrch ishm).

(* ---- what the map claims ------------------------------------------------- *)

Variable pos : memb -> {perm facelet}.

Local Notation wthn := (RowRun.wthn pos).
Local Notation soundat := (RowRun.soundat e8inv e4of par8 par4 pos).

(* ---- the bridge to the cube: RowRun's own -------------------------------- *)

Variable coordP : int -> pst -> Prop.
Variable pstok : pst -> bool.

Hypothesis coord_root : coordP croot sroot.
Hypothesis root_ball : posp sroot \in ball Sset 0.
Hypothesis root_pok : pstok sroot.

Hypothesis coord_step : forall c x k, (to_nat k < nmvn)%N -> pstok x ->
  coordP c x -> coordP (cstep c k) (xstep x k).
Hypothesis xstep_pok : forall x k, (to_nat k < nmvn)%N ->
  pstok x -> pstok (xstep x k).
Hypothesis xstep_pos : forall x k, (to_nat k < nmvn)%N -> pstok x ->
  posp (xstep x k) = (posp x * nth 1%g moves (to_nat k))%g.
Hypothesis leaf_memb : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> membok par8 par4 (tomemb x).
Hypothesis leaf_pos : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> pos (tomemb x) = posp x.

(* ---- and the prepass's bridge: RowRun's own ------------------------------ *)

Variable btmv : int -> int -> int.
Variable hmv : int -> {perm facelet}.

Hypothesis hmv_Sset : forall k, (to_nat k < nhn)%N -> hmv k \in Sset.

Hypothesis grpmvP : forall k v bt', (to_nat k < nhn)%N ->
  (bt' <? nbit48i) ->
  ~~ (Uint63.land (RowMap.grpmv cfl msw mlo mhi k v) (bitof bt') =? 0) ->
  exists2 bt, (bt <? nbit48i) &
    btmv k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0).

Hypothesis prep_move : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  inrange (RowMap.pgmv cpg k pg) (RowMap.grmv mgr k gr) (btmv k bt) /\
  pos (unplc (RowMap.pgmv cpg k pg) (RowMap.grmv mgr k gr) (btmv k bt))
  = (pos (unplc pg gr bt) * hmv k)%g.

(* ---- the search with the cuts, which is RowRun.srch_sound with two more    *)
(*      branches, each closed by the hypothesis it was given ---------------- *)

(* WHAT IS NOT CLAIMED: nothing here says the cuts lose no member.  They do   *)
(* lose members.  What is proved is that the map filled.                      *)
Local Notation srchki := (RowSrch.srchki e8num e4bit F frep fsym twsym
                            dnlo dnhi fllo flhi cstep xstep tomemb okmv
                            csolved ishm).
Local Notation srchski := (RowSrch.srchski e8num e4bit F frep fsym twsym
                             dnlo dnhi fllo flhi cstep xstep tomemb okmv
                             csolved ishm).
Local Notation levelski := (RowSrch.levelski e8num e4bit prep
                              F frep fsym twsym dnlo dnhi fllo flhi
                              cstep xstep tomemb okmv csolved croot sroot
                              dsrch ishm).
Local Notation runski := (RowSrch.runski e8num e4bit prep
                            F frep fsym twsym dnlo dnhi fllo flhi
                            cstep xstep tomemb okmv csolved croot sroot
                            dsrch ishm).

(* ---- hcoset's last level --------------------------------------------------- *)

(* As in RowFoldRunC: at the last move the child is handed straight to the    *)
(* search at nought -- the solved test and the mark -- with no table read.    *)
(* Soundness is srchk_sound at nought; the int searches are equal to these.   *)

Fixpoint srchkL (cut : bool) (togo : nat) (c : int) (x : pst) (msk pv : int)
               (m : rmap) : rmap :=
  if togo is togo'.+1 then
    if togo' is 0 then
      ifold nmvn 0
        (fun k m' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
           else if ~~ okmv pv k then m'
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then m'
           else srchk cut 0 (cstep c k) (xstep x k) 0 k m')
        m
    else
    ifold nmvn 0
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
         else if ~~ okmv pv k then m'
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if [&& (nd <= togo')%N
               & [|| ~~ cut, (nd == togo')%N | (rcuti <= togo' + nd)%N]]
           then srchkL cut togo' c' (xstep x k) (wmask w (togo' - nd)) k m'
           else m')
      m
  else srchk cut 0 c x msk pv m.

Fixpoint srchskL (cut : bool) (togo : nat) (c : int) (x : pst) (msk pv : int)
                (enough : int) (mn : rmap * int) : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    if togo' is 0 then
      ifold nmvn 0
        (fun k a =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
           else if ~~ okmv pv k then a
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then a
           else srchsk cut 0 (cstep c k) (xstep x k) 0 k enough a)
        mn
    else
    ifold nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmv pv k then a
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if [&& (nd <= togo')%N
               & [|| ~~ cut, (nd == togo')%N | (rcuti <= togo' + nd)%N]]
           then srchskL cut togo' c' (xstep x k) (wmask w (togo' - nd)) k
                       enough a
           else a)
      mn
  else srchsk cut 0 c x msk pv enough mn.

Fixpoint srchkiL (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                (msk pv : int) (m : rmap) : rmap :=
  if togo is togo'.+1 then
    if togo' is 0 then
      ifold nmvn 0
        (fun k m' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
           else if ~~ okmv pv k then m'
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then m'
           else srchki cut 0 0 (cstep c k) (xstep x k) 0 k m')
        m
    else
    let togoi' := Uint63.sub togoi 1 in
    ifold nmvn 0
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
         else if ~~ okmv pv k then m'
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           (* && is a function and native_compute is call by value, so        *)
           (* a conjunction pays all its tests at every node.  Nested,        *)
           (* the cut test is reached only by a node that passes two.         *)
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else rcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then srchkiL cut togo' togoi' c' (xstep x k)
                       (wmask w (sslack (Uint63.sub togoi' nd))) k m'
           else m')
      m
  else srchki cut 0 togoi c x msk pv m.

Fixpoint srchskiL (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                 (msk pv : int) (enough : int) (mn : rmap * int)
                 : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    if togo' is 0 then
      ifold nmvn 0
        (fun k a =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
           else if ~~ okmv pv k then a
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then a
           else srchski cut 0 0 (cstep c k) (xstep x k) 0 k enough a)
        mn
    else
    let togoi' := Uint63.sub togoi 1 in
    ifold nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmv pv k then a
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           (* && is a function and native_compute is call by value, so        *)
           (* a conjunction pays all its tests at every node.  Nested,        *)
           (* the cut test is reached only by a node that passes two.         *)
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else rcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then srchskiL cut togo' togoi' c' (xstep x k)
                        (wmask w (sslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else srchski cut 0 togoi c x msk pv enough mn.

Lemma lastL_ball x k d : (to_nat k < nmvn)%N -> pstok x -> (1 <= d)%N ->
  posp x \in ball Sset (d - 1) -> posp (xstep x k) \in ball Sset (d - 0).
Proof.
move=> hk hp hd hb; rewrite (xstep_pos hk hp) subn0 -(subnK hd) addn1.
by apply: ball_step; [exact: hb | apply: mv_Sset; exact: hk].
Qed.

Lemma srchkL_sound cut togo c x msk pv m d :
  (togo <= d)%N -> coordP c x -> pstok x ->
  soundat m d -> posp x \in ball Sset (d - togo) ->
  soundat (srchkL cut togo c x msk pv m) d.
Proof.
elim: togo c x msk pv m => [|togo ih] c x msk pv m hdt hc hp hm hb.
  apply: srchk_sound; try eassumption.
case: togo ih hdt hb => [|togo] ih hdt hb.
  apply: (@ifold_indi _ (fun m' => soundat m' d)); [| |exact: hm].
    by apply: ltnW; apply: (@ltn_nwB 5).
  move=> k m' hk hm'.
  case: ifP => _; first exact: hm'.
  case: ifP => _; first exact: hm'.
  case: ifP => _; first exact: hm'.
  apply: srchk_sound; try eassumption.
  - exact: leq0n.
  - exact: coord_step.
  - exact: xstep_pok.
  exact: lastL_ball.
apply: (@ifold_indi _ (fun m' => soundat m' d)); [| |exact: hm].
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

Lemma srchskL_sound cut togo c x msk pv enough mn d :
  (togo <= d)%N -> coordP c x -> pstok x ->
  soundat mn.1 d -> posp x \in ball Sset (d - togo) ->
  soundat (srchskL cut togo c x msk pv enough mn).1 d.
Proof.
elim: togo c x msk pv mn => [|togo ih] c x msk pv mn hdt hc hp hm hb.
  rewrite /srchskL; case: ifP => _; first exact: hm.
  apply: srchsk_sound; try eassumption.
rewrite /srchskL -/srchskL; case: ifP => _; first exact: hm.
case: togo ih hdt hb => [|togo] ih hdt hb.
  apply: (@ifold_indi _ (fun a => soundat a.1 d)); [| |exact: hm].
    by apply: ltnW; apply: (@ltn_nwB 5).
  move=> k a hk ha.
  case: ifP => _; first exact: ha.
  case: ifP => _; first exact: ha.
  case: ifP => _; first exact: ha.
  apply: srchsk_sound; try eassumption.
  - exact: leq0n.
  - exact: coord_step.
  - exact: xstep_pok.
  exact: lastL_ball.
apply: (@ifold_indi _ (fun a => soundat a.1 d)); [| |exact: hm].
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

Lemma srchkiL_eq cut togo :
  forall togoi c x msk pv m, to_nat togoi = togo -> (togo <= 63)%N ->
  srchkiL cut togo togoi c x msk pv m = srchkL cut togo c x msk pv m.
Proof.
elim: togo => [|togo ih] togoi c x msk pv m htg hb.
  by rewrite /srchkiL /srchkL; apply: srchki_eq.
case: togo ih htg hb => [|togo] ih htg hb.
  rewrite /srchkiL /srchkL; apply: ifold_eqf => k m'.
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  by apply: srchki_eq.
rewrite /srchkiL -/srchkiL /srchkL -/srchkL.
cbv zeta; apply: ifold_eqf => k m'.
have hbd : (to_nat togoi < nwB)%N := to_nat_bounded togoi.
have h1t : (to_nat 1 <= to_nat togoi)%N by rewrite to_nat_1 htg.
have htg' : to_nat (Uint63.sub togoi 1) = togo.+1.
  by rewrite (to_nat_sub togoi 1 h1t hbd) to_nat_1 htg subn1.
have ht62 : (togo.+1 <= 62)%N by rewrite -ltnS.
case: ifP => _; first by [].
case: ifP => _; first by [].
case: ifP => _; first by [].
set w := mdist _.
rewrite (condE cut w htg' ht62).
case: ifP => hif; last by [].
have hbd' : (to_nat (Uint63.sub togoi 1) < nwB)%N :=
  to_nat_bounded (Uint63.sub togoi 1).
have hwle : (to_nat w <= to_nat (Uint63.sub togoi 1))%N.
  by rewrite htg'; move: hif => /andP[].
rewrite mmaskiE (to_nat_sub (Uint63.sub togoi 1) w hwle hbd') htg'.
by apply: ih; [exact: htg' | exact: ltnW].
Qed.

Lemma srchskiL_eq cut togo :
  forall togoi c x msk pv enough mn, to_nat togoi = togo -> (togo <= 63)%N ->
  srchskiL cut togo togoi c x msk pv enough mn
  = srchskL cut togo c x msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x msk pv enough mn htg hb.
  rewrite /srchskiL /srchskL; case: ifP => _; first by [].
  by apply: srchski_eq.
rewrite /srchskiL -/srchskiL /srchskL -/srchskL.
case: ifP => _; first by [].
case: togo ih htg hb => [|togo] ih htg hb.
  apply: ifold_eqf => k a.
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  case: ifP => _; first by [].
  by apply: srchski_eq.
cbv zeta; apply: ifold_eqf => k a.
have hbd : (to_nat togoi < nwB)%N := to_nat_bounded togoi.
have h1t : (to_nat 1 <= to_nat togoi)%N by rewrite to_nat_1 htg.
have htg' : to_nat (Uint63.sub togoi 1) = togo.+1.
  by rewrite (to_nat_sub togoi 1 h1t hbd) to_nat_1 htg subn1.
have ht62 : (togo.+1 <= 62)%N by rewrite -ltnS.
case: ifP => _; first by [].
case: ifP => _; first by [].
case: ifP => _; first by [].
set w := mdist _.
rewrite (condE cut w htg' ht62).
case: ifP => hif; last by [].
have hbd' : (to_nat (Uint63.sub togoi 1) < nwB)%N :=
  to_nat_bounded (Uint63.sub togoi 1).
have hwle : (to_nat w <= to_nat (Uint63.sub togoi 1))%N.
  by rewrite htg'; move: hif => /andP[].
rewrite mmaskiE (to_nat_sub (Uint63.sub togoi 1) w hwle hbd') htg'.
by apply: ih; [exact: htg' | exact: ltnW].
Qed.

(* ---- the level with no prepass, and the run ------------------------------ *)

Definition slvlsk (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then
      if (d == dsrch)%N then
        let n0 := mcount m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (srchskL cut d croot sroot (wmask w (d - nd)) 18 e (m', n0)).1
      else srchkL cut d croot sroot (wmask w (d - nd)) 18 m'
    else m'
  else m'.

Fixpoint runskc (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := slvlsk true d.+1 (prep m dst) in
      runskc n1 d.+1 (mcount m') m' m
    else
      let m' := slvlsk false d.+1 m in
      runskc n1 d.+1 (mcount m') m' dst
  else m.

Lemma slvlsk_sound cut m d : soundat m d.+1 -> soundat (slvlsk cut d.+1 m) d.+1.
Proof.
move=> hp; rewrite /slvlsk; cbv zeta.
case: ifP => _; last exact: hp.
case: ifP => _; last exact: hp.
case: ifP => _; last first.
  apply: srchkL_sound; try eassumption; first exact: leqnn.
  by rewrite subnn.
apply: srchskL_sound; try eassumption; first exact: leqnn.
by rewrite subnn.
Qed.

Lemma runskc_sound n d n0 m dst :
  soundat m d -> soundat dst d -> soundat (runskc n d n0 m dst) (d + n).
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hm hd; first by rewrite addn0.
rewrite addnS -addSn /= -/runskc; case: ifP => _.
  apply: ih; last exact: RowRun.soundatW.
  apply: slvlsk_sound; rewrite !prep_eq.
  apply: (RowRun.prepass_sound hmv_Sset grpmvP prep_move hm).
  exact: RowRun.soundatW.
apply: ih; last exact: RowRun.soundatW.
by apply: slvlsk_sound; exact: RowRun.soundatW.
Qed.

(* ---- the same over the int search ----------------------------------------- *)

Definition slvlski (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (sslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := mcount m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (srchskiL cut d di croot sroot msk 18 e (m', n0)).1
      else srchkiL cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint runskic (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := slvlski true d.+1 (prep m dst) in
      runskic n1 d.+1 (mcount m') m' m
    else
      let m' := slvlski false d.+1 m in
      runskic n1 d.+1 (mcount m') m' dst
  else m.

Lemma slvlski_eq cut d m : (d <= 63)%N -> slvlski cut d m = slvlsk cut d m.
Proof.
move=> hb; rewrite /slvlski /slvlsk; cbv zeta.
case: ifP => _; last by [].
have hdw : (d < nwB)%N.
  by apply: (@ltn_nwB 6); [ | exact: hb].
have hd : to_nat (of_nat d) = d := of_natK d hdw.
set w := mdist _.
rewrite nleE hd; case: ifP => hle; last by [].
have hbd : (to_nat (of_nat d) < nwB)%N := to_nat_bounded (of_nat d).
have hwle : (to_nat w <= to_nat (of_nat d))%N by rewrite hd; exact: hle.
rewrite mmaskiE (to_nat_sub (of_nat d) w hwle hbd) hd.
by case: ifP => _; [rewrite srchskiL_eq | rewrite srchkiL_eq].
Qed.

Lemma runskic_eq n d n0 m dst : (d + n <= 63)%N ->
  runskic n d n0 m dst = runskc n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hb; first by [].
have hd1 : (d.+1 <= 63)%N.
  by apply: leq_trans hb; rewrite -addSnnS; exact: leq_addr.
have hb' : (d.+1 + n <= 63)%N by rewrite addSnnS.
rewrite /= -/runskic -/runskc.
by case: ifP => _; rewrite slvlski_eq // ih.
Qed.

End SrchC.
