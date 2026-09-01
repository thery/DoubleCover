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

(* THE PREPASS IS A PARAMETER.  RowMap's is one; RowLvl's prepassD, which     *)
(* reads each page's chunk once and puts it back once, is another and is      *)
(* proved equal to it.  The run takes whichever it is handed.  The proof asks   *)
(* only that it be RowMap's.                                                  *)
Variable prep : rmap -> rmap -> rmap.

Hypothesis prep_eq : forall m dst,
  prep m dst = prepass mpg mgr msw mlo mhi m dst.

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
move=> hm hd; rewrite /levelsk; cbv zeta; rewrite !prep_eq.
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

(* ---- the search that carries the depth is the same search ---------------- *)

(* NOTHING NEW IS PROVED ABOUT THE CUBE.  srchki is shown EQUAL to srchk when *)
(* the int it carries is the depth left, so srchk_sound carries over as it    *)
(* stands.  There are two side conditions and no more: of_nat round trips     *)
(* below nwB, so a bound on the depth travels with it, and neither            *)
(* subtraction wraps.                                                         *)

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

(* two walks that take the same step are the same walk                        *)
Lemma ifold_eqf (A : Type) n j (f g : int -> A -> A) a :
  (forall i b, f i b = g i b) -> ifold n j f a = ifold n j g a.
Proof.
by move=> hfg; elim: n j a => [|n ih] j a //=; rewrite hfg; apply: ih.
Qed.

(* the two tests, as equations rather than views                              *)
Lemma nleE (a b : int) : (a <=? b) = (to_nat a <= to_nat b)%N.
Proof. by apply/nlebP/idP. Qed.

Lemma neqE (a b : int) : (a =? b) = (to_nat a == to_nat b)%N.
Proof. by apply/neqbP/eqP. Qed.

Lemma to_nat2 : to_nat 2 = 2%N.
Proof. by vm_compute. Qed.

Lemma to_nat5 : to_nat 5 = 5%N.
Proof. by vm_compute. Qed.

(* mmask asks its slack whether it is two or more and whether it is one, and  *)
(* nothing else, so the int slack and its nat give the same mask              *)
Lemma mmaskiE w s : wmask w (sslack s) = wmask w (to_nat s).
Proof.
rewrite /sslack; case E2 : (2 <=? s).
  have hs : (2 <= to_nat s)%N by rewrite -to_nat2 -nleE E2.
  by rewrite /mmask hs.
have hs2 : (to_nat s < 2)%N by rewrite -to_nat2 ltnNge -nleE E2.
case E1 : (s =? 1).
  have hs1 : to_nat s = 1%N by rewrite -to_nat_1; apply/eqP; rewrite -neqE E1.
  by rewrite hs1.
have hs0 : to_nat s = 0%N.
  case E : (to_nat s) hs2 => [|n] // hn.
  have hn0 : n = 0%N by move: hn; rewrite ltnS ltnS leqn0 => /eqP.
  by move: E1; rewrite neqE to_nat_1 E hn0 eqxx.
by rewrite hs0.
Qed.


(* the nested tests, against the conjunction they replace.  A lemma of its   *)
(* own because the induction hypothesis mentions cut, so it cannot be taken  *)
(* apart inside the proof.                                                   *)
Lemma condE (cut : bool) (w togoi' : int) (togo : nat) :
  to_nat togoi' = togo -> (togo <= 62)%N ->
  (if w <=? togoi'
   then (if cut
         then (if w =? togoi' then true else rcutii <=? Uint63.add togoi' w)
         else true)
   else false)
  = [&& (to_nat w <= togo)%N
      & [|| ~~ cut, (to_nat w == togo)%N | (rcuti <= togo + to_nat w)%N]].
Proof.
move=> htg ht62.
rewrite nleE htg; case E1 : (to_nat w <= togo)%N; last by [].
rewrite /=; case: cut; last by [].
rewrite /= neqE htg; case E2 : (to_nat w == togo)%N; first by [].
rewrite /=.
have hw : (to_nat w <= togo)%N by rewrite E1.
have hlt : (to_nat togoi' + to_nat w < nwB)%N.
  apply: (@ltn_nwB 8); first by [].
  rewrite htg; apply: (@leq_ltn_trans (62 + 62)%N); last by [].
  by apply: leq_add => //; apply: leq_trans hw ht62.
by rewrite nleE /rcutii /rcuti to_nat5 (to_nat_add togoi' w hlt) htg.
Qed.

(* ---- the search ---------------------------------------------------------- *)

Lemma srchki_eq cut togo :
  forall togoi c x msk pv m, to_nat togoi = togo -> (togo <= 63)%N ->
  srchki cut togo togoi c x msk pv m = srchk cut togo c x msk pv m.
Proof.
elim: togo => [|togo ih] togoi c x msk pv m htg hb; first by [].
rewrite /RowSrch.srchki -/RowSrch.srchki /RowSrch.srchk -/RowSrch.srchk.
cbv zeta; apply: ifold_eqf => k m'.
have hbd : (to_nat togoi < nwB)%N := to_nat_bounded togoi.
have h1t : (to_nat 1 <= to_nat togoi)%N by rewrite to_nat_1 htg.
have htg' : to_nat (Uint63.sub togoi 1) = togo.
  by rewrite (to_nat_sub togoi 1 h1t hbd) to_nat_1 htg subn1.
have ht62 : (togo <= 62)%N by rewrite -ltnS.
case: ifP => _; first by [].
case: ifP => _; first by [].
case: ifP => _; first by [].
set w := mdist _.
rewrite (condE cut w htg' ht62).
case: ifP => hif; last by [].
have hwt : (to_nat w <= togo)%N by move: hif => /andP[].
have hbd' : (to_nat (Uint63.sub togoi 1) < nwB)%N :=
  to_nat_bounded (Uint63.sub togoi 1).
have hwle : (to_nat w <= to_nat (Uint63.sub togoi 1))%N by rewrite htg'.
rewrite mmaskiE (to_nat_sub (Uint63.sub togoi 1) w hwle hbd') htg'.
by apply: ih; [exact: htg' | exact: ltnW].
Qed.

Lemma srchski_eq cut togo :
  forall togoi c x msk pv enough mn, to_nat togoi = togo -> (togo <= 63)%N ->
  srchski cut togo togoi c x msk pv enough mn
  = srchsk cut togo c x msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x msk pv enough mn htg hb; first by [].
rewrite /RowSrch.srchski -/RowSrch.srchski /RowSrch.srchsk -/RowSrch.srchsk.
case: (Uint63.leb enough mn.2); first by [].
cbv zeta; apply: ifold_eqf => k a.
have hbd : (to_nat togoi < nwB)%N := to_nat_bounded togoi.
have h1t : (to_nat 1 <= to_nat togoi)%N by rewrite to_nat_1 htg.
have htg' : to_nat (Uint63.sub togoi 1) = togo.
  by rewrite (to_nat_sub togoi 1 h1t hbd) to_nat_1 htg subn1.
have ht62 : (togo <= 62)%N by rewrite -ltnS.
case: ifP => _; first by [].
case: ifP => _; first by [].
case: ifP => _; first by [].
set w := mdist _.
rewrite (condE cut w htg' ht62).
case: ifP => hif; last by [].
have hwt : (to_nat w <= togo)%N by move: hif => /andP[].
have hbd' : (to_nat (Uint63.sub togoi 1) < nwB)%N :=
  to_nat_bounded (Uint63.sub togoi 1).
have hwle : (to_nat w <= to_nat (Uint63.sub togoi 1))%N by rewrite htg'.
rewrite mmaskiE (to_nat_sub (Uint63.sub togoi 1) w hwle hbd') htg'.
by apply: ih; [exact: htg' | exact: ltnW].
Qed.

(* ---- the level and the run ----------------------------------------------- *)

Lemma levelski_eq cut d m dst : (d <= 63)%N ->
  levelski cut d m dst = levelsk cut d m dst.
Proof.
move=> hb; rewrite /RowSrch.levelski -/RowSrch.levelski.
rewrite /RowSrch.levelsk -/RowSrch.levelsk; cbv zeta.
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

(* the two runs read one level down, and both are reflexivity                 *)
Lemma runskiS n d n0 m dst :
  runski n.+1 d n0 m dst
  = runski n d.+1 (mcount (levelski (Uint63.ltb ncutb n0) d.+1 m dst))
           (levelski (Uint63.ltb ncutb n0) d.+1 m dst) m.
Proof. by []. Qed.

Lemma runskS n d n0 m dst :
  runsk n.+1 d n0 m dst
  = runsk n d.+1 (mcount (levelsk (Uint63.ltb ncutb n0) d.+1 m dst))
          (levelsk (Uint63.ltb ncutb n0) d.+1 m dst) m.
Proof. by []. Qed.

Lemma runski_eq n d n0 m dst : (d + n <= 63)%N ->
  runski n d n0 m dst = runsk n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst hb; first by [].
have hd1 : (d.+1 <= 63)%N.
  by apply: leq_trans hb; rewrite -addSnnS; exact: leq_addr.
rewrite runskiS runskS levelski_eq; last exact: hd1.
rewrite ih; first by [].
by rewrite addSnnS.
Qed.

(* and so the run over that search is sound, on RowSrch's own proof           *)
Lemma runski_sound n d n0 m dst : (d + n <= 63)%N ->
  soundat m d -> soundat dst d -> soundat (runski n d n0 m dst) (d + n).
Proof. by move=> hb hm hd; rewrite runski_eq //; apply: runsk_sound. Qed.

End Srch.
