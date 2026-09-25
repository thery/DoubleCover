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

(* ---- the level with no prepass, and the run ------------------------------ *)

Definition slvlsk (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then
      if (d == dsrch)%N then
        let n0 := mcount m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (srchsk cut d croot sroot (wmask w (d - nd)) 18 e (m', n0)).1
      else srchk cut d croot sroot (wmask w (d - nd)) 18 m'
    else m'
  else m'.

Lemma levelskE cut d m dst : levelsk cut d m dst = slvlsk cut d (prep m dst).
Proof. by []. Qed.

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
  apply: srchk_sound; try eassumption; first exact: leqnn.
  by rewrite subnn.
apply: srchsk_sound; try eassumption; first exact: leqnn.
by rewrite subnn.
Qed.

Lemma runskc_sound n d n0 m dst :
  soundat m d -> soundat dst d -> soundat (runskc n d n0 m dst) (d + n).
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hm hd; first by rewrite addn0.
rewrite addnS -addSn /= -/runskc; case: ifP => _.
  apply: ih; last exact: RowRun.soundatW.
  rewrite -levelskE; apply: levelsk_sound; try eassumption.
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
        (srchski cut d di croot sroot msk 18 e (m', n0)).1
      else srchki cut d di croot sroot msk 18 m'
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
by case: ifP => _; [rewrite srchski_eq | rewrite srchki_eq].
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
