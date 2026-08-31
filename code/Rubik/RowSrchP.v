(* =========================================================================  *)
(*  RowSrchP.v -- the plain search with the cuts and the stop is sound.       *)
(* =========================================================================  *)

(* srchk_sound, srchsk_sound, levelsk_sound and runsk_sound: what RowRun      *)
(* proves of the bare search, proved here of the one RowSrch defines.  It is  *)
(* RowFoldRun.v, written for the unfolded map.                                *)
(*                                                                            *)
(* WHAT IS NOT CLAIMED: nothing here says the cuts lose no member.  They do   *)
(* lose members.  What is proved is that the map filled, and a cut that       *)
(* loses words can only make the row finish later, never call a member        *)
(* covered when it is not.                                                    *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask RowSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section Srch.

(* ---- the layout, the prepass and the table: RowRun's own ----------------- *)

Variable e8num e8inv e4bit e4of par8 par4 : arr.

Hypothesis he8 : e8ok e8num e8inv par8.
Hypothesis he4 : e4ok e4bit e4of par4.

Local Notation plc := (place e8num e4bit).
Local Notation unplc := (unplace e8inv e4of par8 par4).

Variable mpg mgr msw mlo mhi : arr.

Local Notation prep := (prepass mpg mgr msw mlo mhi).

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

(* the moves of H, one bit each                                              *)
Variable ishm : int.

Local Notation p1g := (sp1g F frep fsym twsym).
Local Notation srchk := (RowSrch.srchk e8num e4bit F frep fsym twsym
                           dnlo dnhi fllo flhi cstep xstep tomemb okmv
                           csolved ishm).
Local Notation srchsk := (RowSrch.srchsk e8num e4bit F frep fsym twsym
                            dnlo dnhi fllo flhi cstep xstep tomemb okmv
                            csolved ishm).
Local Notation levelsk := (RowSrch.levelsk e8num e4bit mpg mgr msw mlo mhi
                             F frep fsym twsym dnlo dnhi fllo flhi
                             cstep xstep tomemb okmv csolved croot sroot
                             dsrch ishm).
Local Notation runsk := (RowSrch.runsk e8num e4bit mpg mgr msw mlo mhi
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
  (bt' <? nbiti) ->
  ~~ (Uint63.land (RowMap.grpmv msw mlo mhi k v) (bitof bt') =? 0) ->
  exists2 bt, (bt <? nbiti) &
    btmv k bt = bt' /\ ~~ (Uint63.land v (bitof bt) =? 0).

Hypothesis prep_move : forall k pg gr bt, (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  inrange (RowMap.pgmv mpg k pg) (RowMap.grmv mgr k gr) (btmv k bt) /\
  pos (unplc (RowMap.pgmv mpg k pg) (RowMap.grmv mgr k gr) (btmv k bt))
  = (pos (unplc pg gr bt) * hmv k)%g.

(* ---- the search with the cuts, which is RowRun.srch_sound with two more    *)
(*      branches, each closed by the hypothesis it was given ---------------- *)

(* WHAT IS NOT CLAIMED: nothing here says the cuts lose no member.  They do   *)
(* lose members.  What is proved is that the map filled.                      *)
Lemma srchk_sound cut togo c x msk pv m d :
  (togo <= d)%N -> coordP c x -> pstok x ->
  soundat m d -> posp x \in ball Sset (d - togo) ->
  soundat (srchk cut togo c x msk pv m) d.
Proof.
elim: togo c x msk pv m => [|togo ih] c x msk pv m hdt hc hp hm hb.
  (* a leaf: the position is in H and the three ranks are the member it is *)
  have hG : posp x \in G := subsetP (ball_sub_gen Sset _) _ hb.
  rewrite /=; case: (boolP (csolved c)) => [hs|_]; last exact: hm.
  have hok := leaf_memb hc hp hG hs.
  have E : plc (tomemb x) =
      (mcp (tomemb x),
       Uint63.div (PArray.get e8num (mud (tomemb x))) 2,
       PArray.get e4bit (mmp (tomemb x))) by [].
  move=> pg' gr' bt' hr ht.
  case: (mmarkP (place_range he8 he4 hok E) hr ht) => [[<- <- <-]|hb2];
    last by apply: hm.
  rewrite /RowRun.wthn (unplace_place he8 he4 hok E) (leaf_pos hc hp hG hs).
  by move: hb; rewrite subn0.
(* a step: the same map, one move further out *)
apply: (@ifold_indi _ (fun m' => soundat m' d)); [| |exact: hm].
  by apply: ltnW; apply: (@ltn_nwB 5).
move=> k m' hk hm'.
case: ifP => _; first exact: hm'.
case: ifP => _; first exact: hm'.
(* THE CUT, and it only skips *)
case: ifP => _; first exact: hm'.
cbv zeta; case: ifP => hle; last exact: hm'.
apply: (ih _ _ _ _ _ _ (coord_step hk hp hc) (xstep_pok hk hp) hm');
    first by apply: ltnW.
rewrite (xstep_pos hk hp) -(subnSK hdt).
by apply: ball_step; [exact: hb | apply: mv_Sset; exact: hk].
Qed.

(* ---- the search with the stop, which writes nothing new ------------------ *)

(* the counting mark is the mark, or it is nothing *)
Lemma mmarkn1 mn pg gr bt :
  (mmarkn mn pg gr bt).1 = mmark mn.1 pg gr bt \/
  (mmarkn mn pg gr bt).1 = mn.1.
Proof.
case: mn => m n; rewrite /mmarkn /mmark /gor /=.
by case: ifP => _; [left | right].
Qed.

(* THE LEAF, RESTATED.  `/=' takes the counting mark apart as well as the     *)
(* triple; read through this equation -- which is reflexivity -- the mark is  *)
(* still there to match.                                                      *)
Lemma srchsk0 cut c x msk pv enough mn :
  srchsk cut 0 c x msk pv enough mn =
  (if Uint63.leb enough mn.2 then mn
   else if csolved c
   then mmarkn mn (mcp (tomemb x))
                  (Uint63.div (PArray.get e8num (mud (tomemb x))) 2)
                  (PArray.get e4bit (mmp (tomemb x)))
   else mn).
Proof. by []. Qed.

Lemma srchsk_sound cut togo c x msk pv enough mn d :
  (togo <= d)%N -> coordP c x -> pstok x ->
  soundat mn.1 d -> posp x \in ball Sset (d - togo) ->
  soundat (srchsk cut togo c x msk pv enough mn).1 d.
Proof.
elim: togo c x msk pv mn => [|togo ih] c x msk pv mn hdt hc hp hm hb.
  have hG : posp x \in G := subsetP (ball_sub_gen Sset _) _ hb.
  have E : plc (tomemb x) =
      (mcp (tomemb x),
       Uint63.div (PArray.get e8num (mud (tomemb x))) 2,
       PArray.get e4bit (mmp (tomemb x))) by [].
  rewrite srchsk0.
  (* the stop hands back what it was given *)
  case: ifP => _; first exact: hm.
  case: ifP => [hs|_]; last exact: hm.
  have hok := leaf_memb hc hp hG hs.
  case: (mmarkn1 mn (mcp (tomemb x))
           (Uint63.div (PArray.get e8num (mud (tomemb x))) 2)
           (PArray.get e4bit (mmp (tomemb x)))) => ->; last exact: hm.
  move=> pg' gr' bt' hr ht.
  case: (mmarkP (place_range he8 he4 hok E) hr ht) => [[<- <- <-]|hb2];
    last by apply: hm.
  rewrite /RowRun.wthn (unplace_place he8 he4 hok E) (leaf_pos hc hp hG hs).
  by move: hb; rewrite subn0.
rewrite /srchsk -/srchsk.
case: ifP => _; first exact: hm.
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

(* ---- one level, and the run ---------------------------------------------- *)

Lemma levelsk_sound cut m dst d :
  soundat m d -> soundat dst d.+1 -> soundat (levelsk cut d.+1 m dst) d.+1.
Proof.
move=> hm hd; rewrite /levelsk; cbv zeta.
have hp := RowRun.prepass_sound hmv_Sset grpmvP prep_move hm hd.
case: ifP => _; last exact: hp.
case: ifP => _; last exact: hp.
case: ifP => _; last first.
  apply: (srchk_sound _ coord_root root_pok hp) => //.
  by rewrite subnn.
apply: srchsk_sound.
- exact: leqnn.
- exact: coord_root.
- exact: root_pok.
- exact: hp.
by rewrite subnn.
Qed.

Lemma runsk_sound n d n0 m dst :
  soundat m d -> soundat dst d -> soundat (runsk n d n0 m dst) (d + n).
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hm hd; first by rewrite addn0.
rewrite addnS -addSn /runsk -/runsk; cbv zeta.
apply: ih.
  by apply: levelsk_sound => //; apply: RowRun.soundatW.
by apply: RowRun.soundatW.
Qed.

End Srch.
